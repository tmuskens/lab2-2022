# Lab 2: Authorization & Trust

### Learning goals

* Understand the core techniques that are used to automatically prove theorems like those needed for the authorization logic discussed in lecture.
* Gain experience designing customized automated reasoning techniques for specific instances of authorization policies.
* Develop familiarity with public-key authentication and how certificate authorities are used to establish trust.
* Gain experience identifying flaws in code that deals with authentication decisions, and developing exploits that leverage such flaws.

### Getting started

Clone this repository onto your local machine or your Andrew home directory.

You will need to use Python 3.10 to complete this lab. You can reuse the virtual environment that you created for Lab 1. The only new dependency that you will need to complete the lab is the `cryptography` modulo, which you can install either via `pip` or `conda` from within your environment.
```
> [pip|conda] install cryptography
```
You should then copy your private key into the `private_key` directory of this repository. Assuming `<id>` is your Andrew ID, run the following command:
```
scp <id>@linux.andrew.cmu.edu:/afs/andrew.cmu.edu/usr21/jrduvall/15316-f22/<id>/<id>.pem private_keys
```

## Implementing an authorization prover

### Authorization Logic

The logic is defined in `logic.py`. It is the same authorization logic that we have discussed in class. Note that there are three types of constants: agents, keys, and resources. 
* `Agent` constants are always prefixed with `#`.
* `Key` constants appear between brackets `[]`.
* `Resource` constants appear between angle brackets `<>`.
In formulas, locations expecting a constant of a particular type can also recieve a variable. So both of the following are syntactically valid formulas.
```
A says open(B, R)
#A says open(#B, <R>)
```
A parser is provided in `src/parser.py`, so you can construct, for example, a sequent object by calling:
```
parse('P true, Q true |- A aff Q')
```
Note that writing `true` after truth (`Proposition`) judgements is optional for the parser. When parsing quantified formulas, note that you should surround the quantified formula with parentheses to avoid potential parser errors. So running,
```
parse('@x . @y . open(x, y)')
```
may result in a parser error. It should be run as follows:
```
parse('@x . (@y . (open(x, y)))')
```
The grammar is given below. 
```
<agent>   ::= x                            // variable
            | #a                           // constant
            
<key>     ::= x                            // variable
            | [k]                          // constant
            
<resource> ::= x                           // variable
            | <r>                          // constant

<formula> ::= x                            // variable
            | <formula> -> <formula>       // implication
            | <agent> says <formula>
            | iskey(<agent>, <key>)
            | sign(<formula>, <key>)
            | ca(<agent>)
            | open(<agent>, <resource>)
            | @x . <formula>               // universal quantifier
            
<judgement> ::= <formula> true             // proposition
              | <agent> aff <formula>      // affirmation
              
<sequent> ::= <judgement>* |- <judgement>
```

### Proof goals

For this lab, you will implement a prover that is able to construct authorization proofs for two delegation policies. The environment that these policies assume consists of the following agents:
* `#ca`: the certificate authority
* `#root`: the agent who ultimately provisions authorization
* `#mfredrik`: authorized by `#root` to open `<shared.txt>` and `<secret.txt>`
* `#aditi`: authorized by `#mfredrik` to open `<secret.txt>`
* `#jack`: authorized by `#aditi` to open `<secret.txt>`
* `#nuno`: authorized by `#jack` to open `<secret.txt>`
* `#andrewid`: everyone in the class is authorized by `#root` to open `<andrewid.txt>`, by `#mfredrik` to open `#shared`, and by `#nuno` to open `<secret.txt>`.

You will first want to prove that you are able to open `<andrewid.txt>`, for your Andrew ID.
```
... |- #root says open(#andrewid, <andrewid.txt>)
```
You will then use the basic delegation policy, issued as a credential by `#root`:
```
#root says (@A . ((#mfredrik says open(A, <shared.txt>)) 
                    -> open(A, <shared.txt>)))
```
Your prover should use this policy to prove that you can open `<shared.txt>`:
```
... |- #root says open(#andrewid, <shared.txt>)
```
Finally, your prover will use the transitive delegation policy, also issued by `#root`:
```
#root says (@A . (@R . (open(A, R) -> (@B . ((A says open(B, R)) 
                                        -> open(B, R))))))
```
To prove that you can access `<secret.txt>`:
```
... |- #root says open(#andrewid, <secret.txt>)
```

#### Credentials and Certificates
In each of the sequents that you will prove above, the context (i.e., assumptions to the left of the sequent) is given by the set of credentials and certificates distributed with the lab in the `credentials` and `certs` directories, respectively. 

Each credential is a formula signed by another agent. For example, the following credential is signed by `#root`, and says that `#andrewid` is authorized to open `<andrewid.txt>`.
```
{
  "p": "open(#andrewid, <andrewid.txt>)",
  "signator": "#root",
  "signature": "5abc0a47a09d39e22f37f98791a108add35ca0bf85f84ab0a13462dc9206dddab6fbc4e7a5daf59c425622aa9a6009806983ba5c16d69c40ad5976e95edf230e"
}
```
Each policy in the bulleted list above, as well as the two delegation policies just discussed, has a corresponding credential in this directory. 

Each certificate is a public key, associated with an agent, and signed by the `#ca` agent. The certificate for `#root` is shown below.
```
{
  "agent": "#root",
  "cred": {
    "p": "iskey(#root, [88:02:3f:fb:03:0f:c8:54:dc:75:f0:8e:cc:c3:54:22])",
    "signator": "#ca",
    "signature": "91aa08822ebc913109d4cac15ddfa0165d8a1166cacf303c560d888a245c36fe4873519f3e45e065b551c1de44fc708b5add3713f5188af19720920f9dddca02"
  },
  "public_key": "2d2d2d2d2d424547494e205055424c4943204b45592d2d2d2d2d0a4d436f77425159444b32567741794541644c6c416a767751693954302b543765544f726d524c506f67426f346d34327056483246597877355858773d0a2d2d2d2d2d454e44205055424c4943204b45592d2d2d2d2d0a"
}

```

When you run `auth.py`, your prover will be called after populating the context with all of the credentials in this directory.

Each credential is added as a `sign` formula. For the example credential shown above, if is the public key fingerprint of `#andrewid`, then the following formula is added as an assumption). Note that the key matches the public key fingerprint listed in the certificate for `#root`.
```
sign(open(#andrewid, <andrewid.txt>), [88:02:3f:fb:03:0f:c8:54:dc:75:f0:8e:cc:c3:54:22])
```

Each certificate is added as a `sign(iskey(...))` formula, signed with the key of `#ca`. So the example certificate for `#root` shown above would become the following assumption.
```
sign(
    iskey(#root, [88:02:3f:fb:03:0f:c8:54:dc:75:f0:8e:cc:c3:54:22]),
    [68:d7:6c:b7:95:fb:a4:f7:a7:4f:12:44:6f:27:c5:40]
)
```
Finally, the following assumptions are always added, to establish that `#ca` is the trusted certificate authority, and that their key is already known.
```
ca(#ca)
iskey(#ca, [68:d7:6c:b7:95:fb:a4:f7:a7:4f:12:44:6f:27:c5:40])
```

#### Running `auth.py`

When you run `auth.py`, giving it an `agent` and a `resource` as arguments: 
```
> python src/auth.py agent resource
```
it gathers the assumptions discussed in the previous section into a context `Gamma`, constructs the sequent `Gamma |- #root says open(#agent, <resource>)`, and calls your prover. If your prover finds a proof, then `auth.py` scans the proof to determine which credentials and certificates are *actually* needed, and constructs an authorization request containing your proof along with all of the necessary credentials and certificates to verify it.

You may run `auth.py` with the `-s` flag, and a request will be sent to an authorization server. If your proof verifies, and all of the credentials check out, then you will recieve a credential back from the server letting you know that `#root` grants access.

### Tactics

As discussed in lecture, your prover will make use of a set of tactics that you design to construct authorization proofs. A tactic is simply a class with the following signature:
```
class Tactic(ABC):

    @abstractmethod
    def apply(self, seq: Sequent) -> set[Proof]:
        return set([seq])
```
The `apply` method accepts a sequent, and generates a set of proofs. Several tactics are provided for you in `prover.py`. Consult their documentation strings to learn more about what they do.

For example, we can construct a simple tactic that repeatedly applies the left implication rule and the identity rule:
```
t = RepeatTactic(
        ThenTactic([
            RuleTactic(impLeftRule),
            RuleTactic(identityRule)
        ])
    )
```
This is sufficient to prove basic implication chains, giving results like the following.
```
                          T.0  T.1
->L ---------------------------------------------------
      P true, (P -> Q) true, (Q -> R) true |- R true

Proof T.1:
                        *
id -------------------------------------------
     (P -> Q) true, R true, P true |- R true

Proof T.0:
               *                             *
   id --------------------   id ----------------------------
        P true |- P true          Q true, P true |- Q true
->L ------------------------------------------------------------
                 (P -> Q) true, P true |- Q true
```
However, the tactics provided in the starter code are not sufficient to produce authorization proofs. Crucially, they do not explicitly deal with the `ca`, `iskey` and `sign` formulas that will populate the context, or the universal quantifiers needed to discharge the two delegation policies.

Your task is to implement `prove` in `prover.py` to address these shortcomings. Design one or more tactics that can make use of the `sign` credentials given as assumptions by `auth.py` to prove each of the three authorization claims described in the previous section.
* We encourage you to break this task up into smaller, modular tactics rather than attempting to write a large, monolithic tactic. For example, tactics that deal with converting `sign(...)` formulas into `says` formulas (according to the `Sign` rule) separately from dealing with the quantifiers in the delegation policies will be easier to reason about and debug.
* When thinking about how to handle the delegation policies, consider working backwards through delegation credentials in a goal-oriented fashion. Although it may be tempting to write a tactic that deals with universal quantifiers in a very general way, this approach can be difficult to scale.
* Part of your grade will be calculated by the number of unnecessary credentials and certificates that your authorization requests contain: your proof should not rely on credentials that are not actually needed to make a successful authorization. You should consider this when designing tactics that deal with `sign(...)` formulas: they could all be converted to `says` formulas eagerly before doing anything else, but this would mean that your proof would always rely on *every* certificate and credential provided in the context. It is better to consider tactics that only make use of `sign` formulas when they are needed to make progress handling the delegation policy.
* Study the starter tactics and their comments if you are unsure how to begin. It's fine to start small: write tactics that emulate the steps that you would take to complete a proof by hand, and test them early. Use these tactics as building blocks to handle more complex formulas, until you are able to complete the authorization requests described in the previous section.

#### Testing your prover

The starter code in `prover.py` is configured to run your implementation of `prove` on a set of smaller tests in `prover_tests.txt` when invoked from the command line from the root of this repository.
```
> python src/prover.py
```
These tests are not graded, but we recommend that you start developing your prover with the goal of passing progressively more of these tests. These will be easier to debug than the ultimate authorization goals of the lab, as they have fewer assumptions, and require fewer proof steps to complete. We encourage you to add more tests to this file depending on issues you encounter when developing your tactics.

When you believe that your prover is able to handle the actual delegation policies, run the following commands to construct authorization requests from proofs, and send them to the server:
```
> python src/auth.py -s andrewid andrewid.txt
> python src/auth.py -s andrewid shared.txt
> python src/auth.py -s andrewid secret.txt
```
If you see credentials like the following, then you have successfully completed this part of the lab.
```
************************ Credential ************************
statement: open(#andrewid, <secret.txt>)
signator: #root
signature: [63:7f:5f:b7:11:4e:b8:e7:55:dd:96:01:8d:13:88:75]
************************************************************
```

## Exploiting an authorization vulnerability

When you use `auth.py` to send an authorization request to the server, the server calls `verify_request` to check the credentials and certificates in your request, and ultimately verifies your authorization proof. However, there is a bug in this implementation that can be exploited to allow anybody to convince the server to verify arbitrary access requests.

Familiarize yourself with this code, particularly the implementation of `verify_request`, to identify the vulnerability. Then provide an implementation of `generate_exploit` in `src/exploit.py` that exploits the vulnerability by constructing an `AccessRequest` for the resource `<bigsecret.txt>` that the server will successfully verify. 

You will know that you have completed this task when the server returns the appropriate credential, as shown below (`#andrewid` will be replaced by your ID).

```
************************ Credential ************************
statement: open(#andrewid, <bigsecret.txt>)
signator: #root
signature: [63:7f:5f:b7:11:4e:b8:e7:55:dd:96:01:8d:13:88:75]
************************************************************
```

To see how `AccessRequest` objects are made, consult the documentation for `AccessRequest.make_for_proof` in `crypto.py`. You will need:
* A proof of `|- #root says open(#andrewid, <bigsecret.txt>)`
* The set of credentials needed to prove the above sequent, as `Credential` objects.
* The set of certificates needed to verify the credentials needed for the request.

Note that the credentials provided with the lab will not allow you to prove the sequent listed above. As part of this exploit, you will need to generate one or more credentials and possibly one or more new certificates.
* Credentials are constructed by `Credential.from_formula`. Given a formula `P` and agent `#A`, calling `Credential.from_formula(P, #A)` will return a `Credential` object representing the signature of `P` with the private key of `#A`. The only private key that you have access to is your own, and you should be able to complete the task by calling `from_formula` to sign with your own agent.
* Certificates are constructed by calling `Certificate.make_for_key` with three arguments: a public key to create the certificate for, an agent to associate with the public key, and an agent whose private key will be used to sign the certificate.
* You can also generate new users, with private keys stored locally in `private_keys`, by calling `new_user` in `src/crypto.py`.

You will find code that generates `AccessRequest` objects in `generate_request`, in `auth.py`. You may be able to use this function to construct the request, but it may be more straightforward to use the code in that function as an example to work from.

## Utility code

Before developing your implementation, you should have a look in `util.py`. This file contains several utility functions that are likely to be helpful with the tasks described above.
* `allvars`, `allkeys`, `agents`, and `resources` return sets of variables, keys, agents, or resources contained in formulas, sequents, and proofs.
* `fresh_var` returns a fresh variable that is not named within a formula, sequent, or proof.
* `is_ca_key` scans a sequent to determine whether a specified key belongs to a certificate authority.
* `get_cas` scans a sequent to return the set of agents named as certificate authorities by the `ca(*)` predicate.
* `get_ca_key` scans a sequent to find the set of public key fingerprints that are associated with certificate authorities.
* `is_key` scans a sequent to determine whether a public key fingerprint is associated with a specified agent.
* `is_credential` scans a sequent to determine whether a given formula is a credential signed by a specified agent.
* `has_credential` scans a sequent to determine whether a credential for a given formula, signed by a specified agent, exists in the context.
* There are `*_stringify` functions for formulas, sequents, and proofs. The function `stringify` function can be called on any of these objects, and dispatches to the correct stringifier.
* When calling `stringify` on a proof, you can pass the optional argument `trunc_context=True` to print the proof without the context (i.e., `gamma`) portion of sequents. This can make it easier to follow and debug when attempting to prove sequents with many assumptions.


## What to hand in

Submit your work on Gradescope. Create a `zip` archive of the repository, but make sure that you have not included the directory `lab1-2022` at the root of the archive. Additionally, there is no need to hand in test cases or files in `src/__pycache__`, and doing so may slow down processing by the autograder.

You are encouraged to use the `handin.sh` script, which will create an appropriate archive in `handin.zip` to upload to Gradescope. This script will not work when run from Windows' `cmd.exe` or Powershell, but you may translate it to use native Windows commands if you are not already using the WSL2 setup described at the top of this readme.

## Evaluation

This lab is worth 100 points, and will be graded by a combination of autograder test cases and, when necessary, manual inspection by the course staff. The test cases will use the same delegation policies described in this handout, but with a different set of credentials than those in this repository. We will also test your exploit in `exploit.py`, and ensure that the exploit is not used as a tactic by your prover.

The percentage breakdown is as follows.
* 15 points for a successful proof of `open(#andrewid, <andrewid.txt>)`
* 25 points for a successful proof of `open(#andrewid, <shared.txt>)`
* 35 points for a successful proof of `open(#andrewid, <secret.txt>)`
* 25 points for an exploit that results in `open(#andrewid, <bigsecret.txt>)`

We will additionally check that the credentials used by your proofs for the top three bullets are minimal, i.e., that the access requests generated by your proofs do not send more credentials and certificates than are necessary to make the authorization claim. Proofs that use more credentials than are necessary will recieve 80% of the credit allotted by the corresponding bullet above.