-- Prove2me | solution 1 for PermanentRollout.squareFreeExponent_prod_treeBlockVector
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:09.567922+00:00
-- url     : https://prove2.me/submissions/484a916f-9404-4a4d-9305-7ba6ae36b211

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution {r : ℕ}
    (rows block : Finset (Fin r)) :
    (squareFreeExponent rows).prod
        (fun row n => treeBlockVector block row ^ n) =
      if rows ⊆ block then (1 : ℂ) else 0 := by
  classical
  by_cases hsubset : rows ⊆ block
  · simp only [if_pos hsubset, Finsupp.prod,
      squareFreeExponent_support]
    apply Finset.prod_eq_one
    intro row hrow
    simp [squareFreeExponent_apply, treeBlockVector,
      hrow, hsubset hrow]
  · obtain ⟨row, hrow, hnot⟩ := Finset.not_subset.mp hsubset
    simp only [if_neg hsubset, Finsupp.prod,
      squareFreeExponent_support]
    apply Finset.prod_eq_zero hrow
    simp [squareFreeExponent_apply, treeBlockVector, hrow, hnot]
end PermanentRollout
