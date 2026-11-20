-- Prove2me | solution 1 for P010.orderedPrimeClass_chain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:48:00.786045+00:00
-- url     : https://prove2.me/submissions/89a240c0-9089-4d19-b4f7-2f15a9c2504d

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
public import Theorems.Thm_P010_primeClass_chain
public import Theorems.Thm_P010_orderedPrimeClass_mem

set_option autoImplicit true
@[expose] public section
public section
open P010
namespace P010
theorem _root_.solution (n p u v : ℕ)
    (hp : Nat.Prime p)
    (hu : u ∈ primeClass n p) (hv : v ∈ primeClass n p) :
    NonCoprimeChain (orderedPrimeClass n p u v) := by
  apply primeClass_chain n p hp
  intro m hm
  exact orderedPrimeClass_mem n p u v m hu hv hm
end P010
