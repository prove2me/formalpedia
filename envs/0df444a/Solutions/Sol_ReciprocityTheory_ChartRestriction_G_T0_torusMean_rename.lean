-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.torusMean_rename
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:52:18.056318+00:00
-- url     : https://prove2.me/submissions/16414b3b-058b-4eff-9081-3e69935c6c85

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AevalElimEqRenameLinearSubstitution
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ContinuousTorusPoint
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_measurable_log_eval_torus
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_torusProb_map_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField MeasureTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.Closed
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution {κ κ' : Type} [Fintype κ] [Fintype κ'] (e : κ → κ')
    (he : Function.Injective e) (f : MvPolynomial κ ℂ) :
    torusMean (MvPolynomial.rename e f) = torusMean f := by
  unfold torusMean
  simp_rw [MvPolynomial.eval_rename]
  rw [← torusProb_map_comp e he, MeasureTheory.integral_map]
  · rfl
  · exact (measurable_pi_lambda _ fun i => measurable_pi_apply (e i)).aemeasurable
  · exact (measurable_log_eval_torus f).aestronglyMeasurable
end ReciprocityTheory.ChartRestriction.G.T0
