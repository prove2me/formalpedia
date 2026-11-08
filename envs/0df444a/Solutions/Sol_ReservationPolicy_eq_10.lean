-- Prove2me | solution 1 for ReservationPolicy.eq_10
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:27:58.287399+00:00
-- url     : https://prove2.me/submissions/3e989d16-ef2d-410c-abc4-f832921d00f5

import Mathlib
import Definitions.Def_ReservationPolicy_admittedMean

open MeasureTheory

open ReservationPolicy in
theorem solution (m d : ℝ) (h : |d - m| < 1) :
    admittedMean m d = (1 + d + m) / 2 := by
  obtain ⟨hc1, hc2⟩ := abs_lt.mp h
  have hS : {ε : ℝ | d < m + ε} = Set.Ioi (d - m) := by
    ext ε
    simp only [Set.mem_setOf_eq, Set.mem_Ioi]
    constructor <;> intro h <;> linarith
  have hI : Set.Ioi (d - m) ∩ Set.Icc (-1 : ℝ) 1 = Set.Ioc (d - m) 1 := by
    ext ε
    simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Icc, Set.mem_Ioc]
    constructor
    · rintro ⟨h1, _, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨h1, by linarith, h3⟩
  have hP : admitProb m d = (1 - (d - m)) / 2 := by
    unfold admitProb noise
    rw [hS, measureReal_def, Measure.smul_apply, Measure.restrict_apply measurableSet_Ioi, hI,
      Real.volume_Ioc, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith)]
    norm_num <;> ring
  have hInt : ∫ ε in {ε | d < m + ε}, (m + ε) ∂noise
      = (m * (1 - (d - m)) + (1 ^ 2 - (d - m) ^ 2) / 2) / 2 := by
    unfold noise
    rw [hS, Measure.restrict_smul, integral_smul_measure,
      Measure.restrict_restrict measurableSet_Ioi, hI,
      ← intervalIntegral.integral_of_le hc2.le,
      intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
        (by apply Continuous.intervalIntegrable; fun_prop),
      intervalIntegral.integral_const, integral_id]
    norm_num <;> ring
  unfold admittedMean
  rw [hInt, hP]
  have hpos : 0 < 1 - (d - m) := by linarith
  field_simp <;> ring
