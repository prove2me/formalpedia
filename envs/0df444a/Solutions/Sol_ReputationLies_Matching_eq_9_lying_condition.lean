-- Prove2me | solution 1 for ReputationLies.Matching.eq_9_lying_condition
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T03:36:51.341994+00:00
-- url     : https://prove2.me/submissions/8d93bbb3-68d3-4c80-a0c3-3bc841b689ce

import Mathlib
import Definitions.Def_ReputationLies_Matching_Model

open Set MeasureTheory

open ReputationLies.Matching in
theorem solution (P : Primitives) (hP : P.Standing) (r : ℝ) (hr : 0 < r)
    (σ : Profile) (hσ : IsEquilibrium P σ r) (b : ℝ) :
    utility P σ r b false false < utility P σ r b false true ↔
      P.L r < b * ((P.F σ.sR - P.F σ.sNR) / P.F σ.sR) := by
  obtain ⟨hsL, hsLH, hsH1, -, -, -, -, -, -, -, -, -, -, -, -, -, hμX, hμX1, -, hFmono, -⟩ := hP
  obtain ⟨-, -, -, -, hF, hsR, hsNR, -, -⟩ := hσ
  haveI := hμX
  have hc : P.μX (Icc (0:ℝ) 1)ᶜ = 0 := (prob_compl_eq_zero_iff measurableSet_Icc).mpr hμX1
  have hhire : ∀ (m : Bool) (s : ℝ), (∀ x ∈ Icc (0:ℝ) 1, (σ.σF x m = true ↔ x ≤ s)) →
      hireProb P σ m = P.F s := by
    intro m s hs
    unfold hireProb Primitives.F
    congr 1
    rw [← measure_inter_conull (s := {x | σ.σF x m = true}) hc,
      ← measure_inter_conull (s := Iic s) hc]
    congr 1
    ext x
    simp only [mem_inter_iff, mem_setOf_eq, mem_Iic]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨(hs x h2).mp h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨(hs x h2).mpr h1, h2⟩
  have h1 : hireProb P σ true = P.F σ.sR := hhire true σ.sR (fun x hx => (hF x hx).1)
  have h0 : hireProb P σ false = P.F σ.sNR := hhire false σ.sNR (fun x hx => (hF x hx).2)
  have hFpos : 0 < P.F σ.sR := by
    have hsR0 : 0 < σ.sR := lt_of_lt_of_le hsL hsR.1
    have hmem : σ.sR ∈ Icc (0:ℝ) 1 := ⟨hsR0.le, by linarith [hsR.2]⟩
    have := hFmono ⟨le_refl 0, zero_le_one⟩ hmem hsR0
    have h00 : 0 ≤ P.F 0 := ENNReal.toReal_nonneg
    linarith
  unfold utility
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [h1, h0]
  unfold Primitives.L
  rw [← mul_div_assoc, lt_div_iff₀ hFpos]
  constructor <;> intro h <;> nlinarith
