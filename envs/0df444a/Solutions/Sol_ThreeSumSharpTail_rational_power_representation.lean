-- Prove2me | solution 1 for ThreeSumSharpTail.rational_power_representation
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-13T19:30:01.606735+00:00
-- url     : https://prove2.me/submissions/f0112faa-c165-4c4c-a22c-da3083fc8b78

import Mathlib

private theorem cast_num_abs_div_den (q : ℚ) (hq : 0 < q) :
    (q.num.natAbs : ℝ) / q.den = (q : ℝ) := by
  have hi : (q.num.natAbs : ℤ) = q.num := Int.natAbs_of_nonneg (Rat.num_pos.mpr hq).le
  have hcast : (q.num.natAbs : ℝ) = (q.num : ℝ) := by
    have h := congrArg (fun z : ℤ => (z : ℝ)) hi
    simpa using h
  rw [hcast]
  exact_mod_cast Rat.num_div_den q

/-- Finite natural exponent data and an exact integer-power test for the real regime. -/
theorem solution (a s : ℚ) (ha0 : 0 < a) (ha1 : a < 1)
    (hs0 : 0 < s) (hsHalf : s < 1 / 2) :
    ∃ A B c e : ℕ, 1 ≤ B ∧ 1 ≤ e ∧ A ≤ B ∧ 2 * c ≤ e ∧
      (A : ℝ) / B = (a : ℝ) ∧ (c : ℝ) / e = (s : ℝ) / 2 ∧
      ∀ N D : ℕ, 1 ≤ N → 1 ≤ D →
        ((D : ℝ) ≤ (N : ℝ) ^ (a : ℝ) ↔ D ^ B ≤ N ^ A) := by
  let A := a.num.natAbs
  let B := a.den
  let c := s.num.natAbs
  let e := 2 * s.den
  have hB : 1 ≤ B := a.den_pos
  have he : 1 ≤ e := by dsimp [e]; have := s.den_pos; omega
  have hB0 : (0 : ℝ) < B := Nat.cast_pos.2 hB
  have hsd0 : (0 : ℝ) < s.den := Nat.cast_pos.2 s.den_pos
  have haRep : (A : ℝ) / B = (a : ℝ) := cast_num_abs_div_den a ha0
  have hsRep : (c : ℝ) / s.den = (s : ℝ) := cast_num_abs_div_den s hs0
  have ha1R : (a : ℝ) < 1 := by exact_mod_cast ha1
  have hs1R : (s : ℝ) < 1 := by
    have h : (s : ℝ) < ((1 / 2 : ℚ) : ℝ) := Rat.cast_lt.mpr hsHalf
    norm_num at h
    linarith
  have hab : A ≤ B := by
    have h : (A : ℝ) / B < 1 := by rwa [haRep]
    have h' : (A : ℝ) < B := by simpa using (div_lt_iff₀ hB0).mp h
    exact_mod_cast h'.le
  have hc : c ≤ s.den := by
    have h : (c : ℝ) / s.den < 1 := by rwa [hsRep]
    have h' : (c : ℝ) < s.den := by simpa using (div_lt_iff₀ hsd0).mp h
    exact_mod_cast h'.le
  have hce : 2 * c ≤ e := Nat.mul_le_mul_left 2 hc
  have hse : (c : ℝ) / e = (s : ℝ) / 2 := by
    dsimp [e]
    push_cast
    rw [← hsRep]
    ring
  refine ⟨A, B, c, e, hB, he, hab, hce, haRep, hse, ?_⟩
  intro N D hN hD
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD
  have hroot0 : 0 < (N : ℝ) ^ (a : ℝ) := Real.rpow_pos_of_pos hN0 _
  have haB : (a : ℝ) * B = A := by
    rw [← haRep]
    exact div_mul_cancel₀ _ hB0.ne'
  have hroot : ((N : ℝ) ^ (a : ℝ)) ^ (B : ℝ) = (N ^ A : ℕ) := by
    rw [← Real.rpow_mul hN0.le, haB, Real.rpow_natCast]
    norm_cast
  have hDPow : (D : ℝ) ^ (B : ℝ) = (D ^ B : ℕ) := by rw [Real.rpow_natCast]; norm_cast
  rw [← Real.rpow_le_rpow_iff hD0.le hroot0.le hB0, hroot, hDPow]
  exact Nat.cast_le

#print axioms solution
