-- Prove2me | solution 1 for ReputationLies.Matching.eq_14_fair_gamble
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T10:56:34.308903+00:00
-- url     : https://prove2.me/submissions/0d7f7dcd-2d26-4e13-b19e-c9cdf5d263fd

import Mathlib
import Definitions.Def_ReputationLies_Matching_Model

open Set MeasureTheory ReputationLies.Matching

namespace RepLiesEq14Aux

theorem hire_eq (μ : Measure ℝ) (hμ : μ (Icc (0:ℝ) 1)ᶜ = 0) (f : ℝ → Bool) (s : ℝ)
    (hs : s ∈ Icc (0:ℝ) 1) (hf : ∀ x ∈ Icc (0:ℝ) 1, (f x = true ↔ x ≤ s)) :
    μ {x | f x = true} = μ (Iic s) := by
  rw [← measure_inter_conull (s := {x | f x = true}) hμ,
    ← measure_inter_conull (s := Iic s) hμ]
  congr 1
  ext x
  simp only [mem_inter_iff, mem_ofPred_eq, mem_Iic]
  constructor
  · rintro ⟨h, hx⟩; exact ⟨(hf x hx).1 h, hx⟩
  · rintro ⟨h, hx⟩; exact ⟨(hf x hx).2 h, hx⟩

end RepLiesEq14Aux

open RepLiesEq14Aux in
theorem solution (P : Primitives) (hP : P.Standing) (r : ℝ) (hr : 0 < r)
    (σ : Profile) (hσ : IsEquilibrium P σ r) :
    msgProb P σ false = 1 - msgProb P σ true ∧
    msgProb P σ true * σ.sR + (1 - msgProb P σ true) * σ.sNR = P.shat ∧
    exAnteHireProb P σ =
      msgProb P σ true * P.F σ.sR + (1 - msgProb P σ true) * P.F σ.sNR := by
  obtain ⟨hsL, hsLH, hsH1, hp0, hp1, -, -, -, -, -, -, -, hμB, -, -, -, hμX, hμX1, -⟩ := hP
  obtain ⟨-, -, -, -, hfirm, hsR, hsNR, hbR, hbNR⟩ := hσ
  have hfalse : msgProb P σ false = 1 - msgProb P σ true := by
    simp only [msgProb, sendProb]; simp; ring
  refine ⟨hfalse, ?_, ?_⟩
  · set rt := recProb P σ true with hrt
    set rf := recProb P σ false with hrf
    have rt0 : 0 ≤ rt := ENNReal.toReal_nonneg
    have rf0 : 0 ≤ rf := ENNReal.toReal_nonneg
    have rt1 : rt ≤ 1 := by
      rw [hrt, recProb]; exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
    have rf1 : rf ≤ 1 := by
      rw [hrf, recProb]; exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
    have hq : msgProb P σ true = P.p * rt + (1 - P.p) * rf := by simp [msgProb, sendProb, hrt, hrf]
    have hq' : msgProb P σ false = P.p * (1 - rt) + (1 - P.p) * (1 - rf) := by
      simp [msgProb, sendProb, hrt, hrf]
    have hA : msgProb P σ true * σ.sR = P.p * rt * P.sH + (1 - P.p) * rf * P.sL := by
      rcases lt_or_ge 0 (msgProb P σ true) with h | h
      · rw [hbR h, bayesBelief]
        simp only [sendProb, if_true, ← hrt, ← hrf]
        field_simp
      · have h0 : P.p * rt = 0 := by nlinarith
        have h1 : (1 - P.p) * rf = 0 := by nlinarith
        have : msgProb P σ true = 0 := by linarith
        rw [this, zero_mul, h0, h1]; ring
    have hB : msgProb P σ false * σ.sNR =
        P.p * (1 - rt) * P.sH + (1 - P.p) * (1 - rf) * P.sL := by
      rcases lt_or_ge 0 (msgProb P σ false) with h | h
      · rw [hbNR h, bayesBelief]
        simp only [sendProb, Bool.false_eq_true, if_false, ← hrt, ← hrf]
        field_simp
      · have h0 : P.p * (1 - rt) = 0 := by nlinarith
        have h1 : (1 - P.p) * (1 - rf) = 0 := by nlinarith
        have : msgProb P σ false = 0 := by linarith
        rw [this, zero_mul, h0, h1]; ring
    rw [← hfalse, hA, hB, Primitives.shat]; ring
  · have hcompl : P.μX (Icc (0:ℝ) 1)ᶜ = 0 := by
      rw [measure_compl measurableSet_Icc (measure_ne_top _ _), hμX1, measure_univ]; simp
    have hRI : σ.sR ∈ Icc (0:ℝ) 1 := ⟨by linarith [hsR.1], by linarith [hsR.2]⟩
    have hNRI : σ.sNR ∈ Icc (0:ℝ) 1 := ⟨by linarith [hsNR.1], by linarith [hsNR.2]⟩
    have h1 : hireProb P σ true = P.F σ.sR := by
      unfold hireProb Primitives.F
      rw [hire_eq P.μX hcompl (fun x => σ.σF x true) σ.sR hRI (fun x hx => (hfirm x hx).1)]
    have h2 : hireProb P σ false = P.F σ.sNR := by
      unfold hireProb Primitives.F
      rw [hire_eq P.μX hcompl (fun x => σ.σF x false) σ.sNR hNRI (fun x hx => (hfirm x hx).2)]
    rw [exAnteHireProb, h1, h2, hfalse]
