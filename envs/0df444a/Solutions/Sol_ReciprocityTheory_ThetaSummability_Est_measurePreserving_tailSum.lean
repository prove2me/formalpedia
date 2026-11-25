-- Prove2me | solution 1 for ReciprocityTheory.ThetaSummability.Est.measurePreserving_tailSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:24:13.274947+00:00
-- url     : https://prove2.me/submissions/0e5873d4-dc44-41c5-9fbb-e008eeaa9058

import Definitions.Def_ReciprocityTheory_ThetaSummability_TailSumEstimates_ConeDefs
import Definitions.Def_ReciprocityTheory_ThetaSummability_TailSumEstimates_ConeChange
import Theorems.Thm_ReciprocityTheory_ThetaSummability_Est_det_tailMat

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
theorem _root_.solution :
    MeasurePreserving (tailSum (r := r)) volume volume := by
  refine ⟨continuous_tailSum.measurable, ?_⟩
  rw [tailSum_eq_toLin', Real.map_linearMap_volume_pi_eq_smul_volume_pi]
  · simp [LinearMap.det_toLin', det_tailMat]
  · simp [LinearMap.det_toLin', det_tailMat]
end ReciprocityTheory.ThetaSummability.Est
