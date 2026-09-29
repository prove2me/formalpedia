-- Prove2me | solution 1 for PreorderADI.Correlation.threshold_quasiconvex
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:25:55.275465+00:00
-- url     : https://prove2.me/submissions/5cc29bc7-5475-4385-9557-24cf222a08b4

import Mathlib
import Definitions.Def_PreorderADI_Correlation_Model

open MeasureTheory ProbabilityTheory

namespace PreorderADI.Correlation

lemma aux_tq_pdf_anti (a b : ℝ) (h : b ^ 2 ≤ a ^ 2) : stdNormalPdf a ≤ stdNormalPdf b := by
  unfold stdNormalPdf
  rw [gaussianPDFReal, gaussianPDFReal]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  have h2 : (0:ℝ) < 2 * ((1:NNReal):ℝ) := by norm_num
  rw [div_le_div_iff_of_pos_right h2]
  simp only [sub_zero]
  linarith

lemma aux_tq_sq_le (a u b : ℝ) (h1 : a ≤ u) (h2 : u ≤ b) : u ^ 2 ≤ a ^ 2 ∨ u ^ 2 ≤ b ^ 2 := by
  rcases le_total 0 u with hu | hu
  · right; nlinarith
  · left; nlinarith

lemma aux_tq_eq (P : Params) (ρ : ℝ) :
    threshold P ρ = (-(P.vL * stdNormalPdf P.zL * P.sigmaL) / (2 * P.Delta * P.zL)) /
      stdNormalPdf (2 * P.zL * Real.sqrt (1 - ρ ^ 2) + P.lamL) := by
  unfold threshold
  rw [div_mul_eq_div_div]

end PreorderADI.Correlation

open PreorderADI.Correlation
open MeasureTheory ProbabilityTheory

theorem solution (P : Params) (hP : P.Standing)
    (hz : P.zL ≤ -(P.lamL / 2)) :
    QuasiconvexOn ℝ (Set.Ico (0:ℝ) 1) (threshold P) := by
  have hlam : 0 ≤ P.lamL := div_nonneg hP.muL_pos.le hP.sigmaL_pos.le
  have hzL : P.zL ≤ 0 := by linarith
  have hDelta : 0 ≤ P.Delta := by unfold Params.Delta; linarith [hP.vL_lt_delta_vH]
  have hA : 0 ≤ P.vL * stdNormalPdf P.zL * P.sigmaL := by
    have h0 := gaussianPDFReal_nonneg 0 1 P.zL
    have h1 : 0 ≤ P.vL := by linarith [hP.c_pos, hP.c_lt_vL]
    have h2 := hP.sigmaL_pos.le
    unfold stdNormalPdf
    positivity
  have hK : 0 ≤ -(P.vL * stdNormalPdf P.zL * P.sigmaL) / (2 * P.Delta * P.zL) := by
    apply div_nonneg_of_nonpos
    · linarith
    · have : 0 ≤ 2 * P.Delta := by linarith
      exact mul_nonpos_of_nonneg_of_nonpos this hzL
  have hmono : ∀ x y : ℝ, 0 ≤ x → x ≤ y →
      2 * P.zL * Real.sqrt (1 - x ^ 2) + P.lamL ≤ 2 * P.zL * Real.sqrt (1 - y ^ 2) + P.lamL := by
    intro x y hx hxy
    have : Real.sqrt (1 - y ^ 2) ≤ Real.sqrt (1 - x ^ 2) := by
      apply Real.sqrt_le_sqrt
      nlinarith
    nlinarith
  have hpos : ∀ u, 0 < stdNormalPdf u := fun u => gaussianPDFReal_pos 0 1 u one_ne_zero
  intro r
  apply Set.OrdConnected.convex
  refine ⟨fun x hx y hy z hzI => ?_⟩
  obtain ⟨⟨hx0, hx1⟩, hxr⟩ := hx
  obtain ⟨⟨hy0, hy1⟩, hyr⟩ := hy
  obtain ⟨hxz, hzy⟩ := hzI
  refine ⟨⟨by linarith, by linarith⟩, ?_⟩
  show threshold P z ≤ r
  rcases aux_tq_sq_le _ _ _ (hmono x z hx0 hxz) (hmono z y (by linarith) hzy) with h | h
  · calc threshold P z ≤ threshold P x := by
          rw [aux_tq_eq, aux_tq_eq]
          exact div_le_div_of_nonneg_left hK (hpos _) (aux_tq_pdf_anti _ _ h)
      _ ≤ r := hxr
  · calc threshold P z ≤ threshold P y := by
          rw [aux_tq_eq, aux_tq_eq]
          exact div_le_div_of_nonneg_left hK (hpos _) (aux_tq_pdf_anti _ _ h)
      _ ≤ r := hyr
