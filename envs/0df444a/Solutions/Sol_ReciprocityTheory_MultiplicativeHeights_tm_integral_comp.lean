-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.tm_integral_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:50:34.438807+00:00
-- url     : https://prove2.me/submissions/c01194a5-1d90-45c1-bf69-2c77d276b841

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusMeanA
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusMeanB
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_measurable_tmUpd
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
    ∫ θ, F θ ∂(torusProb ι) = ∫ p, F (tmUpd i p) ∂((torusProb ι).prod unitIntervalMeasure) := by
  have hmap := (measurePreserving_tmUpd i).map_eq
  conv_lhs => rw [← hmap]
  exact integral_map (measurable_tmUpd i).aemeasurable (by rwa [hmap])
end ReciprocityTheory.MultiplicativeHeights
