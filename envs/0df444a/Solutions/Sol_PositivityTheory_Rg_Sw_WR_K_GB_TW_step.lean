-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.K.GB.TW.step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:53:42.845012+00:00
-- url     : https://prove2.me/submissions/160d39e8-7da0-4a5b-a961-5277f8006487

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_Lagr
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBTwist
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_TW_dirC_mul
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_TW_dirC_const_mul
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_TW_dirC_sum
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_TW_dirC_exp
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_TW_dirC_zero
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_TW_diff_of
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_TW_contDiff_Lc
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_TW_contDiff_W_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.K PositivityTheory.Rg.Sw.WR.K.GB
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR
open PositivityTheory.Rg.Sw.WR.K.GB.TW
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.K.GB.TW
theorem _root_.solution (z : ℂ) (k l : Fin n) (c : ℕ → E n → ℂ) (M : ℕ) (hc : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (c j))
    (hM : ∀ j, M ≤ j → c j = 0) :
    Dkl k l (fun y => W z y * ∑ j ∈ Finset.range M, z ^ j * c j y) =
      fun y => W z y * ∑ j ∈ Finset.range (M + 1), z ^ j * TD k l c j y := by
  funext y
  have hd : ∀ j, DifferentiableAt ℝ (c j) y := fun j => diff_of (hc j) y
  have hdz : ∀ j, DifferentiableAt ℝ (fun x => z ^ j * c j x) y := fun j => (hd j).const_mul _
  have hS : DifferentiableAt ℝ (fun x => ∑ j ∈ Finset.range M, z ^ j * c j x) y :=
    DifferentiableAt.fun_sum fun j _ => hdz j
  have hL : DifferentiableAt ℝ (Lc (n := n)) y := diff_of contDiff_Lc y
  have hW : dirC (W z) (vkl k l) y = W z y * (-z * om k l y) := by
    unfold W
    rw [dirC_exp (hL.const_mul _), dirC_const_mul hL]
    rfl
  have hcM : dirC (c M) (vkl k l) y = 0 := by rw [hM M le_rfl]; exact dirC_zero _ _
  unfold Dkl
  rw [dirC_mul (diff_of (contDiff_W_apply z) y) hS, dirC_sum _ (fun j _ => hdz j), hW]
  simp only [TD, mul_sub, Finset.sum_sub_distrib]
  rw [Finset.sum_range_succ, Finset.sum_range_succ']
  simp only [sh, mul_zero, Dkl, hcM, add_zero, pow_zero, one_mul]
  have e1 : ∀ j ∈ Finset.range M, dirC (fun x => z ^ j * c j x) (vkl k l) y = z ^ j * dirC (c j) (vkl k l) y :=
    fun j _ => dirC_const_mul (hd j) _ _
  rw [Finset.sum_congr rfl e1]
  have key : ∑ j ∈ Finset.range M, z ^ (j + 1) * (om k l y * c j y) =
      z * om k l y * ∑ j ∈ Finset.range M, z ^ j * c j y := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [key]
  ring
end PositivityTheory.Rg.Sw.WR.K.GB.TW
