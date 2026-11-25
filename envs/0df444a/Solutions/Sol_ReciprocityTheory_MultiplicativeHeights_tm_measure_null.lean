-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.tm_measure_null
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:50:39.188402+00:00
-- url     : https://prove2.me/submissions/42facf3a-45da-4f71-ac48-7b1cdaf1e4ed

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
theorem _root_.solution (i : ι) {S : Set (ι → ℝ)} (hS : MeasurableSet S)
    (h : ∀ᵐ θ ∂(torusProb ι), unitIntervalMeasure {t | update θ i t ∈ S} = 0) : torusProb ι S = 0 := by
  rw [← (measurePreserving_tmUpd i).measure_preimage hS.nullMeasurableSet,
    Measure.prod_apply ((measurable_tmUpd i) hS)]
  have h2 : (fun θ => unitIntervalMeasure (Prod.mk θ ⁻¹' (tmUpd i ⁻¹' S))) =ᵐ[torusProb ι] 0 :=
    h.mono fun θ hθ => hθ
  rw [lintegral_congr_ae h2]
  simp
end ReciprocityTheory.MultiplicativeHeights
