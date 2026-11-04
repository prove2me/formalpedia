-- Prove2me | solution 1 for ThreeSum.OutputKeyMasks.eval_outside
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:20:34.134664+00:00
-- url     : https://prove2.me/submissions/bef3abf0-23c0-4ffc-810f-8e64aa5f94a0

import Definitions.Def_Submission_ThreeSum_GlobalKeyEnumeration
import Definitions.Def_Submission_ThreeSum_BlockCoefficientRows
import Definitions.Def_Submission_ThreeSum_OutputKeyMasks
import Theorems.Thm_ThreeSum_OutputKeyMasks_extend_zero
import Theorems.Thm_ThreeSum_OneHotMask_eval_subsetMask


set_option autoImplicit false
open ThreeSum ThreeSum.OutputKeyMasks
open GlobalEncoding LocalHashMoments LocalCoverBounds
open OneHotMask SubsetAddress
open scoped BigOperators
namespace ThreeSum.OutputKeyMasks
theorem _root_.solution {L : ℕ} (Q : Finset (Fin L)) (w : Fin L → ℕ) :
    (eval (extend w) (fun _ => 0) L (subsetMask Q) : ℤ) =
      ∑ i : Fin L, if i ∈ Q then (0 : ℤ) else (w i : ℤ) := by
  rw [← extend_zero L,eval_subsetMask]
  push_cast
  rfl
end ThreeSum.OutputKeyMasks
