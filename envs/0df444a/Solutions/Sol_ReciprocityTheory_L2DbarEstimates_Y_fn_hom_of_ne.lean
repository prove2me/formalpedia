-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.fn_hom_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:59:23.300832+00:00
-- url     : https://prove2.me/submissions/351556a0-8818-457c-9eb2-79bbc8782c75

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ContinuousOnSec
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ImportsAlt
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatNullA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fn_sum_le_totalDegree
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_LogPshAt_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas Set
open scoped ContDiff ENNReal
noncomputable section
universe u
variable {n : ℕ} (De : MvPolynomial (Fin n) ℂ)
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution {a : ℂ} (ha : a ≠ 0) (b : Fin n → ℂ) :
    fnHom De a b = a ^ (De.totalDegree + 1) * MvPolynomial.eval (fun k => b k / a) De := by
  unfold fnHom
  rw [MvPolynomial.eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hle := fn_sum_le_totalDegree De hm
  have hsplit : a ^ (De.totalDegree + 1) = a ^ (De.totalDegree + 1 - ∑ k, m k) * a ^ (∑ k, m k) := by
    rw [← pow_add]
    congr 1
    omega
  have key : (∏ k, (b k / a) ^ m k) * a ^ (∑ k, m k) = ∏ k, b k ^ m k := by
    rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero _ ha)]
  rw [hsplit, ← key]
  ac_rfl
end ReciprocityTheory.L2DbarEstimates.Y
