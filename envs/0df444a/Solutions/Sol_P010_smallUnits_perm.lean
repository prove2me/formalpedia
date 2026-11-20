-- Prove2me | solution 1 for P010.smallUnits_perm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:52:02.382574+00:00
-- url     : https://prove2.me/submissions/35499a74-d5a7-4763-ab0f-296c864b6ab3

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
public import Theorems.Thm_P010_smallEvenUnit_perm

set_option autoImplicit true
@[expose] public section
public section
open P010
namespace P010
theorem _root_.solution (n : ℕ) (small : List ℕ)
    (hsmall : ∀ p ∈ small, Nat.Prime p ∧ 4 * p ≤ n) :
    (small.map (smallEvenUnit n)).flatten.Perm (classConcat n small) := by
  change (small.flatMap (smallEvenUnit n)).Perm
    (small.flatMap (fun p => (primeClass n p).toList))
  apply List.Perm.flatMap_left
  intro p hp
  obtain ⟨hprime, hbound⟩ := hsmall p hp
  exact smallEvenUnit_perm n p hprime hbound
end P010
