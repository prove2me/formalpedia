-- Prove2me | solution 1 for P010.primeClass_chain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:45:47.469149+00:00
-- url     : https://prove2.me/submissions/86b76de3-0aee-4711-90f7-ca67bea2d84d

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
public import Theorems.Thm_P010_prime_class_chain
public import Theorems.Thm_P010_primeClass_dvd

set_option autoImplicit true
@[expose] public section
public section
open P010
namespace P010
theorem _root_.solution (n p : ℕ) (hp : Nat.Prime p)
    (a : List ℕ) (hclass : ∀ m ∈ a, m ∈ primeClass n p) :
    NonCoprimeChain a := by
  apply prime_class_chain p hp a
  intro m hm
  exact primeClass_dvd (hclass m hm)
end P010
