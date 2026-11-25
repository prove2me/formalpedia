-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.H.skodaHyp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:17:04.088169+00:00
-- url     : https://prove2.me/submissions/283c49f5-0310-469a-bfaa-0d1333c510fd

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_HlinVsqPos
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_LeviVA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_SmoothRLog
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_vsq_pos
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_skodaDbar
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_skodaWeight
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_re

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.L2DbarEstimates.H
open MeasureTheory ReciprocityTheory.L2DbarEstimates
open scoped ENNReal InnerProductSpace ContDiff
private theorem sum_conj_mul_perp_eq_zero {p : ℕ} (w a : Fin p → ℂ) (hw : vsq w ≠ 0) :
    ∑ j, (starRingEnd ℂ) (w j) * perp w a j = 0 := by
  have hs : ∑ j, (starRingEnd ℂ) (w j) * w j = ((vsq w : ℝ) : ℂ) := by
    simp only [vsq, Complex.ofReal_sum, Complex.ofReal_pow, Complex.conj_mul']
  have hw' : ((vsq w : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hw
  have h1 : ∑ j, (starRingEnd ℂ) (w j) * perp w a j =
      ∑ j, (starRingEnd ℂ) (w j) * a j - (∑ j, (starRingEnd ℂ) (w j) * w j) *
        ((∑ j, (starRingEnd ℂ) (w j) * a j) / ((vsq w : ℝ) : ℂ)) := by
    simp only [perp]
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  rw [h1, hs, mul_div_cancel₀ _ hw', sub_self]
private theorem norm_perp_apply_sq_le {p : ℕ} (w a : Fin p → ℂ) (i : Fin p) (hw : w ≠ 0) :
    ‖perp w a i‖ ^ 2 ≤ (1 - ‖w i‖ ^ 2 / vsq w) * vsq (perp w a) := by
  have hW : 0 < vsq w := vsq_pos w hw
  have horth := sum_conj_mul_perp_eq_zero w a hW.ne'
  have hsplit : (starRingEnd ℂ) (w i) * perp w a i +
      ∑ j ∈ Finset.univ.erase i, (starRingEnd ℂ) (w j) * perp w a j = 0 :=
    (Finset.add_sum_erase Finset.univ (fun j => (starRingEnd ℂ) (w j) * perp w a j)
      (Finset.mem_univ i)).trans horth
  have hneg : (starRingEnd ℂ) (w i) * perp w a i =
      -∑ j ∈ Finset.univ.erase i, (starRingEnd ℂ) (w j) * perp w a j := by
    linear_combination hsplit
  have hA : ‖w i‖ * ‖perp w a i‖ ≤ ∑ j ∈ Finset.univ.erase i, ‖w j‖ * ‖perp w a j‖ := by
    calc ‖w i‖ * ‖perp w a i‖ = ‖(starRingEnd ℂ) (w i) * perp w a i‖ := by
          rw [norm_mul, Complex.norm_conj]
      _ = ‖∑ j ∈ Finset.univ.erase i, (starRingEnd ℂ) (w j) * perp w a j‖ := by
          rw [hneg, norm_neg]
      _ ≤ ∑ j ∈ Finset.univ.erase i, ‖(starRingEnd ℂ) (w j) * perp w a j‖ := norm_sum_le _ _
      _ = ∑ j ∈ Finset.univ.erase i, ‖w j‖ * ‖perp w a j‖ := by
          simp only [norm_mul, Complex.norm_conj]
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ.erase i) (fun j => ‖w j‖)
    (fun j => ‖perp w a j‖)
  have h0 : 0 ≤ ‖w i‖ * ‖perp w a i‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have h2 : (‖w i‖ * ‖perp w a i‖) ^ 2 ≤ (∑ j ∈ Finset.univ.erase i, ‖w j‖ ^ 2) *
      ∑ j ∈ Finset.univ.erase i, ‖perp w a j‖ ^ 2 := by
    nlinarith [mul_le_mul hA hA h0 (le_trans h0 hA), hCS]
  have hWs : ‖w i‖ ^ 2 + ∑ j ∈ Finset.univ.erase i, ‖w j‖ ^ 2 = vsq w :=
    Finset.add_sum_erase Finset.univ (fun j => ‖w j‖ ^ 2) (Finset.mem_univ i)
  have hVs : ‖perp w a i‖ ^ 2 + ∑ j ∈ Finset.univ.erase i, ‖perp w a j‖ ^ 2 =
      vsq (perp w a) :=
    Finset.add_sum_erase Finset.univ (fun j => ‖perp w a j‖ ^ 2) (Finset.mem_univ i)
  have h3 : vsq w * ‖perp w a i‖ ^ 2 ≤ (vsq w - ‖w i‖ ^ 2) * vsq (perp w a) := by
    rw [← hWs, ← hVs]
    nlinarith [h2]
  rw [one_sub_div hW.ne', div_mul_eq_mul_div, le_div_iff₀ hW]
  nlinarith [h3]
end ReciprocityTheory.L2DbarEstimates.H
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.H
open MeasureTheory ReciprocityTheory.L2DbarEstimates
open scoped ENNReal InnerProductSpace ContDiff
namespace ReciprocityTheory.L2DbarEstimates.H
theorem _root_.solution (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M] :
    SkodaHypStatement n M := by
  unfold SkodaHypStatement
  intro z hz p g φ₀ t u hg hu hg0 hφ hL ht x i ξ
  rw [skodaDbar n M z hz p g u hg hu hg0 x i ξ]
  have hW := (skodaWeight n M z hz p g φ₀ t hg hg0 hφ hL ht.le).2.2 x ξ
  rw [show g i x = gv g x i from rfl]
  generalize (Levi n z (skW g φ₀ t) x ξ).re = L at hW ⊢
  generalize jacM n z g x ξ = a at hW ⊢
  have hw0 := hg0 x
  generalize gv g x = w at hw0 hW ⊢
  have hWp : 0 < vsq w := vsq_pos w hw0
  have hWn : vsq w ≠ 0 := hWp.ne'
  have htn : t ≠ 0 := ht.ne'
  have hn : ‖((vsq w : ℝ) : ℂ)‖ = vsq w := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hWp]
  have hLHS : ‖u x * (starRingEnd ℂ) (perp w a i) / ((vsq w : ℝ) : ℂ)‖ ^ 2 =
      ‖u x‖ ^ 2 * ‖perp w a i‖ ^ 2 / vsq w ^ 2 := by
    rw [norm_div, norm_mul, Complex.norm_conj, hn]
    ring
  rw [hLHS]
  have key := norm_perp_apply_sq_le w a i hw0
  have hwi : ‖w i‖ ^ 2 ≤ vsq w := by
    unfold vsq
    exact Finset.single_le_sum (f := fun j => ‖w j‖ ^ 2) (fun j _ => by positivity)
      (Finset.mem_univ i)
  have hc : 0 ≤ 1 - ‖w i‖ ^ 2 / vsq w := sub_nonneg.mpr ((div_le_one hWp).mpr hwi)
  have hU : 0 ≤ ‖u x‖ ^ 2 := by positivity
  calc ‖u x‖ ^ 2 * ‖perp w a i‖ ^ 2 / vsq w ^ 2
      ≤ ‖u x‖ ^ 2 * ((1 - ‖w i‖ ^ 2 / vsq w) * vsq (perp w a)) / vsq w ^ 2 := by
        gcongr
    _ = ‖u x‖ ^ 2 * (1 - ‖w i‖ ^ 2 / vsq w) / (t * vsq w) *
          (t * (vsq (perp w a) / vsq w)) := by
        field_simp <;> ring
    _ ≤ ‖u x‖ ^ 2 * (1 - ‖w i‖ ^ 2 / vsq w) / (t * vsq w) * L :=
        mul_le_mul_of_nonneg_left hW (div_nonneg (mul_nonneg hU hc) (mul_pos ht hWp).le)
end ReciprocityTheory.L2DbarEstimates.H
