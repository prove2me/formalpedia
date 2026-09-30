-- Prove2me | solution 1 for WeierstrassEllipticZeta.quotient_drazin_zero_unit_criteria
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-10T03:00:34.091517+00:00
-- url     : https://prove2.me/submissions/abc91f45-64fd-416a-981c-5763b5153c5f

import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Tactic.Ring



theorem solution
    (A : Type*) [CommRing A] (I : Ideal A) (p : A) (b : A ⧸ I) (d : ℕ)
    (h₁ : Ideal.Quotient.mk I p * b * b = b)
    (h₂ : (Ideal.Quotient.mk I p) ^ (d + 1) * b = (Ideal.Quotient.mk I p) ^ d) :
    (b = 0 ↔ p ∈ I.radical) ∧
      (IsUnit (Ideal.Quotient.mk I p) ↔ Ideal.Quotient.mk I p * b = 1) := by
  constructor
  · constructor
    · intro hb
      refine Ideal.mem_radical_iff.mpr ⟨d, ?_⟩
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [map_pow]
      simpa only [hb, mul_zero] using h₂.symm
    · intro hp
      obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hp
      have ha : IsNilpotent (Ideal.Quotient.mk I p) := by
        refine ⟨n, ?_⟩
        rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
        exact hn
      have hab : IsNilpotent (Ideal.Quotient.mk I p * b) :=
        (Commute.all _ _).isNilpotent_mul_right ha
      apply hab.isUnit_one_sub.mul_right_cancel
      rw [zero_mul]
      calc
        b * (1 - Ideal.Quotient.mk I p * b) = b - Ideal.Quotient.mk I p * b * b := by ring
        _ = 0 := by rw [h₁, sub_self]
  · constructor
    · intro ha
      apply (ha.pow d).mul_left_cancel
      rw [← mul_assoc, ← pow_succ, h₂, mul_one]
    · intro hb
      exact isUnit_iff_exists_inv.mpr ⟨b, hb⟩

