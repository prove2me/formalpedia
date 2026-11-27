-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.rm_levi_re_ofReal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:31:04.899657+00:00
-- url     : https://prove2.me/submissions/52b4c84e-8b16-4332-b934-e4383f419f3c

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_RegMaxA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_rm_wd_wdb_ofReal
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_rm_bil_expand
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_rm_bil_sum
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_rm_I_smul_vec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
variable {n : ℕ}
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution (F : V n → ℝ) (y : V n) (hF : ContDiffAt ℝ 2 F y) (ξ : Fin n → ℂ) :
    4 * (leviV n (fun x => (F x : ℂ)) y ξ).re =
      fderiv ℝ (fderiv ℝ F) y (rmVec ξ) (rmVec ξ) +
        fderiv ℝ (fderiv ℝ F) y (Complex.I • rmVec ξ) (Complex.I • rmVec ξ) := by
  rw [rm_I_smul_vec]
  unfold rmVec
  rw [rm_bil_sum, rm_bil_sum, ← Finset.sum_add_distrib]
  unfold leviV
  rw [Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_add_distrib, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [rm_wd_wdb_ofReal F y hF j k, rm_bil_expand (fderiv ℝ (fderiv ℝ F) y) (ξ j) (ξ k),
    rm_bil_expand (fderiv ℝ (fderiv ℝ F) y) (Complex.I * ξ j) (Complex.I * ξ k)]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  simp [Complex.mul_re, Complex.mul_im]
  ring
end ReciprocityTheory.L2DbarEstimates.Y
