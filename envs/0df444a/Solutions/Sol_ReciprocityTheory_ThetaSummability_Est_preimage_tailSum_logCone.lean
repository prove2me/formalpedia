-- Prove2me | solution 1 for ReciprocityTheory.ThetaSummability.Est.preimage_tailSum_logCone
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:08:08.171609+00:00
-- url     : https://prove2.me/submissions/e7a32752-8b43-4fa7-8f9b-2be3779153e8

import Definitions.Def_ReciprocityTheory_ThetaSummability_TailSumEstimates_ConeDefs
import Definitions.Def_ReciprocityTheory_ThetaSummability_TailSumEstimates_ConeChange
import Theorems.Thm_ReciprocityTheory_ThetaSummability_Est_tailSum_mem_logCone_iff

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
theorem _root_.solution (c : ℝ) : tailSum ⁻¹' logCone r c = lowerBox r c := by
  ext y; exact tailSum_mem_logCone_iff c y
end ReciprocityTheory.ThetaSummability.Est
