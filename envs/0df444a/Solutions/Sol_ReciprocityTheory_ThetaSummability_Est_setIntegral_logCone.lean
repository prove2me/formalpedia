-- Prove2me | solution 1 for ReciprocityTheory.ThetaSummability.Est.setIntegral_logCone
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:33:21.530424+00:00
-- url     : https://prove2.me/submissions/aa741d64-f0bf-4265-9923-cf51770d469b

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
    ∫ x in logCone r c, f x = ∫ y in lowerBox r c, f (tailSum y) := by
  rw [← preimage_tailSum_logCone c,
    measurePreserving_tailSum.setIntegral_preimage_emb measurableEmbedding_tailSum]
end ReciprocityTheory.ThetaSummability.Est
