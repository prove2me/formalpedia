-- Prove2me | solution 1 for P010.exact_of_matching_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:54:00.279642+00:00
-- url     : https://prove2.me/submissions/f630dee2-7b7e-41eb-bd37-dc4964a81515

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
public import Theorems.Thm_P010_h_le_of_permutation
public import Theorems.Thm_P010_le_h_of_lower_bound

set_option autoImplicit true
@[expose] public section
public section
open P010
namespace P010
theorem _root_.solution (n : ℕ)
    (hlower : ∀ a : List ℕ, IsPermutation n a → target n ≤ adjacentCount a)
    (hupper : ∃ a : List ℕ, IsPermutation n a ∧ adjacentCount a ≤ target n) :
    h n = target n := by
  apply Nat.le_antisymm
  · obtain ⟨a, ha, hscore⟩ := hupper
    exact (h_le_of_permutation n a ha).trans hscore
  · exact le_h_of_lower_bound n (target n) hlower
end P010
