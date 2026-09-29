-- Prove2me | solution 1 for PreorderADI.Correlation.threshold_increasing
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:11:08.072982+00:00
-- url     : https://prove2.me/submissions/56ac66ed-b8a7-4e26-9635-1a0822ada4cc

import Mathlib
import Definitions.Def_PreorderADI_Correlation_Model

open MeasureTheory ProbabilityTheory

namespace PreorderADI.Correlation

lemma aux_thrinc_pdf_pos (x : ℝ) : 0 < stdNormalPdf x := by
  unfold stdNormalPdf
  exact gaussianPDFReal_pos 0 1 x one_ne_zero

lemma aux_thrinc_pdf_anti {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    stdNormalPdf b < stdNormalPdf a := by
  unfold stdNormalPdf
  rw [gaussianPDFReal_def]
  simp only
  have hK : 0 < (√(2 * Real.pi * ((1 : NNReal) : ℝ)))⁻¹ := by positivity
  apply mul_lt_mul_of_pos_left _ hK
  apply Real.exp_lt_exp.mpr
  have h1 : a ^ 2 < b ^ 2 := by nlinarith
  have h2 : (0:ℝ) < 2 * ((1 : NNReal) : ℝ) := by norm_num
  rw [div_lt_div_iff_of_pos_right h2]
  simp only [sub_zero]
  linarith

lemma aux_thrinc_eq (P : Params) (ρ : ℝ) :
    threshold P ρ = (P.vL * stdNormalPdf P.zL * P.sigmaL) /
      ((2 * P.Delta * (-P.zL)) * stdNormalPdf (2 * P.zL * Real.sqrt (1 - ρ ^ 2) + P.lamL)) := by
  unfold threshold
  rw [← neg_div_neg_eq]
  congr 1
  · ring
  · ring

end PreorderADI.Correlation

open PreorderADI.Correlation
open MeasureTheory ProbabilityTheory

theorem solution (P : Params) (hP : P.Standing)
    (hz : -(P.lamL / 2) < P.zL) (hz0 : P.zL < 0) :
    StrictMonoOn (threshold P) (Set.Ico (0:ℝ) 1) := by
  intro r1 hr1 r2 hr2 hlt
  obtain ⟨h1a, h1b⟩ := hr1
  obtain ⟨h2a, h2b⟩ := hr2
  rw [aux_thrinc_eq, aux_thrinc_eq]
  have hvL : 0 < P.vL := lt_trans hP.c_pos hP.c_lt_vL
  have hD : 0 < P.Delta := by unfold Params.Delta; linarith [hP.vL_lt_delta_vH]
  have hM : 0 < P.vL * stdNormalPdf P.zL * P.sigmaL := by
    have := aux_thrinc_pdf_pos P.zL
    have := hP.sigmaL_pos
    positivity
  have hE : 0 < 2 * P.Delta * (-P.zL) := by
    have : 0 < -P.zL := by linarith
    positivity
  -- square roots
  have hs2 : 0 < 1 - r2 ^ 2 := by nlinarith
  have hsq : r1 ^ 2 < r2 ^ 2 := by nlinarith
  have hsl : Real.sqrt (1 - r2 ^ 2) < Real.sqrt (1 - r1 ^ 2) :=
    Real.sqrt_lt_sqrt hs2.le (by linarith)
  have hs1le : Real.sqrt (1 - r1 ^ 2) ≤ 1 := by
    rw [Real.sqrt_le_one]; nlinarith
  have hw1 : 0 < 2 * P.zL * Real.sqrt (1 - r1 ^ 2) + P.lamL := by
    nlinarith [Real.sqrt_nonneg (1 - r1 ^ 2)]
  have hw12 : 2 * P.zL * Real.sqrt (1 - r1 ^ 2) + P.lamL <
      2 * P.zL * Real.sqrt (1 - r2 ^ 2) + P.lamL := by
    nlinarith
  have hphi := aux_thrinc_pdf_anti hw1 hw12
  apply div_lt_div_of_pos_left hM
  · exact mul_pos hE (aux_thrinc_pdf_pos _)
  · exact mul_lt_mul_of_pos_left hphi hE
