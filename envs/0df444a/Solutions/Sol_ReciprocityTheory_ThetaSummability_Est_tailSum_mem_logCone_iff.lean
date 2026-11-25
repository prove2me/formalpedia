-- Prove2me | solution 1 for ReciprocityTheory.ThetaSummability.Est.tailSum_mem_logCone_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:58:33.195628+00:00
-- url     : https://prove2.me/submissions/b12c4bd5-9e79-4d96-8610-4dd634c898a6

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
theorem _root_.solution (c : ℝ) (y : Fin r → ℝ) :
    tailSum y ∈ logCone r c ↔ y ∈ lowerBox r c := by
  simp [logCone, lowerBox, gap_tailSum, Pi.le_def]
end ReciprocityTheory.ThetaSummability.Est
