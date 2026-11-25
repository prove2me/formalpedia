-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gaM_integral_fsDens
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:08:27.333843+00:00
-- url     : https://prove2.me/submissions/a430d8f2-a1fe-4688-9305-9d8ab9c36c5f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFS
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AMassStA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_gaM_lintegral_pi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open MeasureTheory Set Filter Topology
open scoped ENNReal
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution (D : ℕ) :
    ∫ y : Fin D → ℂ, ((1 + ∑ i, ‖y i‖ ^ 2) ^ (D + 1))⁻¹ = Real.pi ^ D / (D.factorial : ℝ) := by
  have hnn : ∀ y : Fin D → ℂ, 0 ≤ ((1 + ∑ i, ‖y i‖ ^ 2) ^ (D + 1))⁻¹ := fun y => by positivity
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hnn)
    (Continuous.aestronglyMeasurable (by
      refine Continuous.inv₀ (by fun_prop) fun y => ?_
      have : 0 < 1 + ∑ i, ‖y i‖ ^ 2 := by positivity
      positivity))]
  have := gaM_lintegral_pi D 1 one_pos 0
  simp only [add_zero, Nat.factorial_zero, Nat.cast_one, mul_one, one_pow] at this
  rw [this, ENNReal.toReal_ofReal (by positivity)]
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
