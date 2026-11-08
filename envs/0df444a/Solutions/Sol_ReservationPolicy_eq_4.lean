-- Prove2me | solution 1 for ReservationPolicy.eq_4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:36:32.623521+00:00
-- url     : https://prove2.me/submissions/4f650ac0-9347-4e30-9e7e-ea159f40f21c

import Mathlib
import Definitions.Def_ReservationPolicy_admitProb

open MeasureTheory

open ReservationPolicy in
theorem solution (m d : ℝ) (h : |d - m| < 1) :
    admitProb m d = (1 - d + m) / 2 := by
  have h1 := (abs_lt.mp h).1
  have h2 := (abs_lt.mp h).2
  unfold admitProb noise
  rw [measureReal_def, Measure.smul_apply, Measure.restrict_apply' measurableSet_Icc]
  have hset : {ε : ℝ | d < m + ε} ∩ Set.Icc (-1) 1 = Set.Ioc (d - m) 1 := by
    ext ε
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Icc, Set.mem_Ioc]
    constructor
    · rintro ⟨ha, _, hb⟩
      exact ⟨by linarith, hb⟩
    · rintro ⟨ha, hb⟩
      exact ⟨by linarith, by linarith, hb⟩
  rw [hset, Real.volume_Ioc, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith),
    ENNReal.toReal_inv, ENNReal.toReal_ofNat]
  ring
