-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.leviV_eq_dv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:13:56.265119+00:00
-- url     : https://prove2.me/submissions/d3247ae8-6764-4b9c-8a6d-e61158c2dee5

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_OfRealNormSqSumMul
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LogNormSq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_sum_wdb_eq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_sum_wd_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology Complex
open scoped ContDiff ENNReal ComplexConjugate
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution {n : ℕ} {g : V n → ℂ} {y : V n} (hg : ContDiffAt ℝ 2 g y) (ξ : Fin n → ℂ) :
    leviV n g y ξ =
      dv (fderiv ℝ (fun v => dbv (fderiv ℝ g v) (WithLp.toLp 2 ξ)) y) (WithLp.toLp 2 ξ) := by
  have hF : DifferentiableAt ℝ (fderiv ℝ g) y :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hd : ∀ k, DifferentiableAt ℝ (wdb n k g) y := by
    intro k
    unfold wdb
    have h1 : DifferentiableAt ℝ (fun v => fderiv ℝ g v (bas n k)) y :=
      hF.clm_apply (differentiableAt_const _)
    have h2 : DifferentiableAt ℝ (fun v => fderiv ℝ g v (I • bas n k)) y :=
      hF.clm_apply (differentiableAt_const _)
    have h3 : DifferentiableAt ℝ
        (fun v => fderiv ℝ g v (bas n k) + I * fderiv ℝ g v (I • bas n k)) y :=
      h1.add (h2.const_mul I)
    simpa only [div_eq_mul_inv] using h3.mul_const (2⁻¹ : ℂ)
  have hsum : (fun v => dbv (fderiv ℝ g v) (WithLp.toLp 2 ξ)) =
      fun v => ∑ k, wdb n k g v * conj (ξ k) := by
    funext v
    rw [← sum_wdb_eq]
  have hD : HasFDerivAt (fun v => ∑ k, wdb n k g v * conj (ξ k))
      (∑ k, conj (ξ k) • fderiv ℝ (wdb n k g) y) y :=
    HasFDerivAt.fun_sum fun k _ => (hd k).hasFDerivAt.mul_const (conj (ξ k))
  rw [hsum, ← sum_wd_eq]
  unfold leviV
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [wd]
  rw [hD.fderiv]
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul',
    Pi.smul_apply, smul_eq_mul, WithLp.ofLp_toLp]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  change _ = _ * ξ j
  ring
end ReciprocityTheory.L2DbarEstimates.Y
