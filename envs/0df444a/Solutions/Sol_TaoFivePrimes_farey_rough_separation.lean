-- Prove2me | solution 1 for TaoFivePrimes.farey_rough_separation
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-09-14T01:55:51.734095+00:00
-- url     : https://prove2.me/submissions/23ec1b9c-d808-46d4-8e59-fd0805d04a50

import Mathlib

open Finset

section PartL46B
open Finset
namespace TaoL46B

/-- Two Farey points built from a small denominator `q0 ≤ Q` and a `Q`-rough denominator
`q1 ≤ R` cannot be closer than `1/(Q^2R^2)` unless the rough parts agree modulo `1`. -/
theorem farey_separation (Q R : ℕ)
    (q0 q0' q1 q1' : ℕ) (a0 a0' a1 a1' : ℤ)
    (hq0 : 0 < q0) (hq0Q : q0 ≤ Q) (hq0' : 0 < q0') (hq0'Q : q0' ≤ Q)
    (hq1 : 0 < q1) (hq1R : q1 ≤ R) (hq1' : 0 < q1') (hq1'R : q1' ≤ R)
    (hrough : ∀ p : ℕ, p.Prime → p ≤ Q → ¬ p ∣ q1)
    (hrough' : ∀ p : ℕ, p.Prime → p ≤ Q → ¬ p ∣ q1')
    (hclose : ∃ k : ℤ,
      |((a0 : ℝ) / q0 + (a1 : ℝ) / q1 - (a0' : ℝ) / q0' - (a1' : ℝ) / q1') - (k : ℝ)|
        < 1 / ((Q : ℝ) ^ 2 * (R : ℝ) ^ 2)) :
    ((q1 : ℤ) * q1') ∣ (a1 * q1' - a1' * q1) := by
  obtain ⟨k, hk⟩ := hclose
  have hq0R : (0 : ℝ) < (q0 : ℝ) := by exact_mod_cast hq0
  have hq0'R : (0 : ℝ) < (q0' : ℝ) := by exact_mod_cast hq0'
  have hq1R' : (0 : ℝ) < (q1 : ℝ) := by exact_mod_cast hq1
  have hq1'R' : (0 : ℝ) < (q1' : ℝ) := by exact_mod_cast hq1'
  -- the common denominator
  set D : ℤ := (q0 : ℤ) * q1 * q0' * q1' with hD
  have hDpos : (0 : ℤ) < D := by positivity
  have hDR : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hDpos
  set N : ℤ := a0 * q1 * q0' * q1' + a1 * q0 * q0' * q1'
      - a0' * q0 * q1 * q1' - a1' * q0 * q1 * q0' with hN
  have hxN : ((a0 : ℝ) / q0 + (a1 : ℝ) / q1 - (a0' : ℝ) / q0' - (a1' : ℝ) / q1')
      = (N : ℝ) / (D : ℝ) := by
    rw [hN, hD]
    push_cast
    field_simp
  -- `D` is at most `Q^2 R^2`
  have hDle : (D : ℝ) ≤ (Q : ℝ) ^ 2 * (R : ℝ) ^ 2 := by
    have h1 : (q0 : ℝ) ≤ Q := by exact_mod_cast hq0Q
    have h2 : (q0' : ℝ) ≤ Q := by exact_mod_cast hq0'Q
    have h3 : (q1 : ℝ) ≤ R := by exact_mod_cast hq1R
    have h4 : (q1' : ℝ) ≤ R := by exact_mod_cast hq1'R
    have hDeq : (D : ℝ) = ((q0 : ℝ) * q0') * ((q1 : ℝ) * q1') := by rw [hD]; push_cast; ring
    have hA : (q0 : ℝ) * q0' ≤ (Q : ℝ) ^ 2 := by nlinarith
    have hB : (q1 : ℝ) * q1' ≤ (R : ℝ) ^ 2 := by nlinarith
    rw [hDeq]
    exact mul_le_mul hA hB (by positivity) (by positivity)
  -- hence `N = D k`
  have hNDk : N = D * k := by
    have hQR : (0 : ℝ) < (Q : ℝ) ^ 2 * (R : ℝ) ^ 2 := lt_of_lt_of_le hDR hDle
    have hstep : |(N : ℝ) - (D : ℝ) * (k : ℝ)| < 1 := by
      have hh : |(N : ℝ) / (D : ℝ) - (k : ℝ)| < 1 / ((Q : ℝ) ^ 2 * (R : ℝ) ^ 2) := by
        rw [← hxN]; exact hk
      have heq : (N : ℝ) - (D : ℝ) * (k : ℝ) = (D : ℝ) * ((N : ℝ) / (D : ℝ) - (k : ℝ)) := by
        field_simp
      rw [heq, abs_mul, abs_of_pos hDR]
      calc (D : ℝ) * |(N : ℝ) / (D : ℝ) - (k : ℝ)|
          < (D : ℝ) * (1 / ((Q : ℝ) ^ 2 * (R : ℝ) ^ 2)) := by
            exact mul_lt_mul_of_pos_left hh hDR
        _ ≤ ((Q : ℝ) ^ 2 * (R : ℝ) ^ 2) * (1 / ((Q : ℝ) ^ 2 * (R : ℝ) ^ 2)) := by
            exact mul_le_mul_of_nonneg_right hDle (by positivity)
        _ = 1 := by rw [mul_one_div, div_self hQR.ne']
    have hint : |N - D * k| < 1 := by
      have h' : ((N - D * k : ℤ) : ℝ) = (N : ℝ) - (D : ℝ) * (k : ℝ) := by push_cast; ring
      have h'' : |((N - D * k : ℤ) : ℝ)| < 1 := by rw [h']; exact hstep
      rw [← Int.cast_abs] at h''
      exact_mod_cast h''
    have hlt := abs_lt.mp hint
    omega
  -- the key divisibility, after clearing the small denominators
  have hkey : (a1 * q1' - a1' * q1) * ((q0 : ℤ) * q0')
      = ((q1 : ℤ) * q1') * (k * q0 * q0' - a0 * q0' + a0' * q0) := by
    have := hNDk
    rw [hN, hD] at this
    linarith [this]
  -- the two denominators are coprime
  have hcop : Nat.Coprime (q1 * q1') (q0 * q0') := by
    by_contra hcon
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hcon
    have hp1 : p ∣ q1 * q1' := hpd.trans (Nat.gcd_dvd_left _ _)
    have hp0 : p ∣ q0 * q0' := hpd.trans (Nat.gcd_dvd_right _ _)
    have hple : p ≤ Q := by
      rcases (Nat.Prime.dvd_mul hp).mp hp0 with h | h
      · exact le_trans (Nat.le_of_dvd hq0 h) hq0Q
      · exact le_trans (Nat.le_of_dvd hq0' h) hq0'Q
    rcases (Nat.Prime.dvd_mul hp).mp hp1 with h | h
    · exact hrough p hp hple h
    · exact hrough' p hp hple h
  have hcopZ : IsCoprime ((q1 : ℤ) * q1') ((q0 : ℤ) * q0') := by
    have := Nat.isCoprime_iff_coprime.mpr hcop
    push_cast at this
    exact this
  exact hcopZ.dvd_of_dvd_mul_right ⟨_, hkey⟩

end TaoL46B
end PartL46B

theorem solution (Q R : ℕ)
    (q0 q0' q1 q1' : ℕ) (a0 a0' a1 a1' : ℤ)
    (hq0 : 0 < q0) (hq0Q : q0 ≤ Q) (hq0' : 0 < q0') (hq0'Q : q0' ≤ Q)
    (hq1 : 0 < q1) (hq1R : q1 ≤ R) (hq1' : 0 < q1') (hq1'R : q1' ≤ R)
    (hrough : ∀ p : ℕ, p.Prime → p ≤ Q → ¬ p ∣ q1)
    (hrough' : ∀ p : ℕ, p.Prime → p ≤ Q → ¬ p ∣ q1')
    (hclose : ∃ k : ℤ,
      |((a0 : ℝ) / q0 + (a1 : ℝ) / q1 - (a0' : ℝ) / q0' - (a1' : ℝ) / q1') - (k : ℝ)|
        < 1 / ((Q : ℝ) ^ 2 * (R : ℝ) ^ 2)) :
    ((q1 : ℤ) * q1') ∣ (a1 * q1' - a1' * q1) :=
  TaoL46B.farey_separation Q R q0 q0' q1 q1' a0 a0' a1 a1' hq0 hq0Q hq0' hq0'Q
    hq1 hq1R hq1' hq1'R hrough hrough' hclose
