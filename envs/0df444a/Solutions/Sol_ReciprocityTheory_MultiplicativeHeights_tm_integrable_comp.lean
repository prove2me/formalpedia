-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.tm_integrable_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:56:59.62251+00:00
-- url     : https://prove2.me/submissions/a147ea5a-af15-4b36-bfaf-e24ee6ef1ece

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusMeanA
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusMeanB
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_measurePreserving_tmUpd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory Real Function
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution (i : ι) {F : (ι → ℝ) → ℝ} (hF : AEStronglyMeasurable F (torusProb ι)) :
    Integrable (F ∘ tmUpd i) ((torusProb ι).prod unitIntervalMeasure) ↔ Integrable F (torusProb ι) := by
  exact (measurePreserving_tmUpd i).integrable_comp hF
end ReciprocityTheory.MultiplicativeHeights
