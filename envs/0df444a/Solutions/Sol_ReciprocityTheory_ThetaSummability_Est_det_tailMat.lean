-- Prove2me | solution 1 for ReciprocityTheory.ThetaSummability.Est.det_tailMat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:13:12.676717+00:00
-- url     : https://prove2.me/submissions/9d07973d-ab5b-4303-9ac7-75c0013091bf

import Definitions.Def_ReciprocityTheory_ThetaSummability_TailSumEstimates_ConeDefs
import Definitions.Def_ReciprocityTheory_ThetaSummability_TailSumEstimates_ConeChange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ThetaSummability ReciprocityTheory.ThetaSummability.Est
open MeasureTheory Finset
variable {r : ℕ}
namespace ReciprocityTheory.ThetaSummability.Est
theorem _root_.solution : (tailMat r).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular]
  · simp [tailMat]
  · intro i j hij
    have : ¬ i ≤ j := not_le.mpr hij
    simp [tailMat, this]
end ReciprocityTheory.ThetaSummability.Est
