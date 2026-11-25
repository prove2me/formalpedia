-- Prove2me | solution 1 for ReciprocityTheory.ThetaSummability.Est.integrableOn_logCone_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:33:17.779398+00:00
-- url     : https://prove2.me/submissions/d5d36305-9be0-437f-b8ef-7220665fa428

import Definitions.Def_ReciprocityTheory_ThetaSummability_TailSumEstimates_ConeDefs
import Definitions.Def_ReciprocityTheory_ThetaSummability_TailSumEstimates_ConeChange
import Theorems.Thm_ReciprocityTheory_ThetaSummability_Est_measurePreserving_tailSum
import Theorems.Thm_ReciprocityTheory_ThetaSummability_Est_measurableEmbedding_tailSum
import Theorems.Thm_ReciprocityTheory_ThetaSummability_Est_preimage_tailSum_logCone

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
theorem _root_.solution (c : ℝ) (f : (Fin r → ℝ) → ℝ) :
    IntegrableOn f (logCone r c) ↔ IntegrableOn (fun y => f (tailSum y)) (lowerBox r c) := by
  rw [← preimage_tailSum_logCone c]
  exact (measurePreserving_tailSum.integrableOn_comp_preimage measurableEmbedding_tailSum).symm
end ReciprocityTheory.ThetaSummability.Est
