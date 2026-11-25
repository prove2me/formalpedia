-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.fn_eq_zero_of_eval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:10:49.629223+00:00
-- url     : https://prove2.me/submissions/3ec61c34-80a4-4df3-b0f7-4a78d6aed0ce

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ContinuousOnSec
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ImportsAlt
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatNullA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fn_hom_zero
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_ident

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.L2DbarEstimates.Y.fn_hom_zero

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas Set
open scoped ContDiff ENNReal
noncomputable section
universe u
variable {n : ℕ} (De : MvPolynomial (Fin n) ℂ)
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution {v0 : V n}
    (h : ∀ᶠ v in 𝓝 v0, MvPolynomial.eval (fun k => v k) De = 0) : De = 0 := by
  have hF : ∀ p : MvPolynomial (Fin n) ℂ,
      Differentiable ℂ (fun v : V n => MvPolynomial.eval (fun k => v k) p) := by
    intro p
    induction p using MvPolynomial.induction_on
    next a =>
      simp only [MvPolynomial.eval_C]
      exact differentiable_const a
    next p q hp hq =>
      simp only [map_add]
      exact hp.add hq
    next p i hp =>
      simp only [map_mul, MvPolynomial.eval_X]
      have hi : Differentiable ℂ (fun v : V n => v i) := by fun_prop
      exact hp.mul hi
  have hEq := ReciprocityTheory.L2DbarEstimates.C.ident n Set.univ (fun v : V n => MvPolynomial.eval (fun k => v k) De) v0
    isOpen_univ convex_univ (hF De).differentiableOn (Set.mem_univ _) h
  apply MvPolynomial.funext
  intro x
  have := hEq (Set.mem_univ (WithLp.toLp 2 x))
  simpa using this
end ReciprocityTheory.L2DbarEstimates.Y
