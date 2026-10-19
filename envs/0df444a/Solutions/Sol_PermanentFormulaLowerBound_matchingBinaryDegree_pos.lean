-- Prove2me | solution 1 for PermanentFormulaLowerBound.matchingBinaryDegree_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.22648+00:00
-- url     : https://prove2.me/submissions/138c6d8c-d0ab-4fbb-be6d-cec78de98f94

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_matchingBinaryDegree_erase_add

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
namespace PermanentFormulaLowerBound
theorem _root_.solution {ell : ℕ}
    (P : Finset (Fin ell)) (hP : P.Nonempty) :
    0 < matchingBinaryDegree P := by
  classical
  obtain ⟨u, hu⟩ := hP
  rw [← matchingBinaryDegree_erase_add P u hu]
  exact Nat.add_pos_right _ (Nat.pow_pos Nat.two_pos)
end PermanentFormulaLowerBound
