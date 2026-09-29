-- Prove2me | solution 1 for TaoFivePrimes.sin_lower_bound_small_divisor
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-09-14T04:19:34.280598+00:00
-- url     : https://prove2.me/submissions/274574b1-58ed-4ea8-ad60-38418b99eb25

import Mathlib
import Theorems.Thm_TaoFivePrimes_two_norm_le_abs_sin_le_pi_norm

open Finset

section PartS5
open Finset
namespace TaoS5

/-- The distance to the nearest integer is `1`-Lipschitz. -/
theorem dist_int_sub (u v : ℝ) :
    |u - round u| - |v| ≤ |(u + v) - round (u + v)| := by
  have h : |u - (round (u + v) : ℝ)| ≤ |(u + v) - round (u + v)| + |v| := by
    have : u - (round (u + v) : ℝ) = ((u + v) - round (u + v)) + (-v) := by ring
    rw [this]
    calc |((u + v) - (round (u + v) : ℝ)) + (-v)|
        ≤ |(u + v) - (round (u + v) : ℝ)| + |(-v)| := abs_add_le _ _
      _ = |(u + v) - round (u + v)| + |v| := by rw [abs_neg]
  have h2 : |u - round u| ≤ |u - (round (u + v) : ℝ)| :=
    round_le u (round (u + v))
  linarith

/-- Doubling at most doubles the distance to the nearest integer. -/
theorem dist_int_two_mul (t : ℝ) : |2 * t - round (2 * t)| ≤ 2 * |t - round t| := by
  have h : |2 * t - ((2 * round t : ℤ) : ℝ)| ≤ 2 * |t - round t| := by
    have : 2 * t - ((2 * round t : ℤ) : ℝ) = 2 * (t - round t) := by push_cast; ring
    rw [this, abs_mul]
    norm_num
  exact le_trans (round_le (2 * t) (2 * round t)) h

/-- A fraction `k/q` with `q` not dividing `k` is at distance at least `1/q` from `ℤ`. -/
theorem dist_int_fraction {k : ℤ} {q : ℕ} (hq : 0 < q) (h : ¬ (q : ℤ) ∣ k) :
    1 / (q : ℝ) ≤ |(k : ℝ) / q - round ((k : ℝ) / q)| := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  set m : ℤ := round ((k : ℝ) / q) with hm
  have hne : k - (q : ℤ) * m ≠ 0 := by
    intro hcon
    exact h ⟨m, by linarith [hcon]⟩
  have h1 : (1 : ℝ) ≤ |((k - (q : ℤ) * m : ℤ) : ℝ)| := by
    have hz : (1 : ℤ) ≤ |k - (q : ℤ) * m| := Int.one_le_abs hne
    calc (1:ℝ) = ((1 : ℤ) : ℝ) := by norm_num
      _ ≤ ((|k - (q : ℤ) * m| : ℤ) : ℝ) := by exact_mod_cast hz
      _ = |((k - (q : ℤ) * m : ℤ) : ℝ)| := by push_cast [Int.cast_abs]; ring
  have h2 : (k : ℝ) / q - (m : ℝ) = ((k - (q : ℤ) * m : ℤ) : ℝ) / (q : ℝ) := by
    push_cast
    field_simp
  rw [h2, abs_div, abs_of_pos hqR]
  rw [div_le_div_iff_of_pos_right hqR]
  exact h1

/-- **Tao, Section 5, equations (5.13)–(5.14)**: for `d ≤ q/2` the frequency `4dα` stays
`1/(2q)` away from the integers, and consequently `|sin(2πdα)| ≥ 1/(2q)`. -/
theorem sin_lower_small_d
    (alpha beta : ℝ) (a : ℤ) (q : ℕ) (hq : 2 ≤ q)
    (haq : Nat.Coprime a.natAbs q)
    (halpha : 4 * alpha = (a : ℝ) / q + beta)
    (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2)
    (d : ℕ) (hd1 : 1 ≤ d) (hd2 : 2 * d ≤ q) :
    1 / (2 * (q : ℝ)) ≤ |4 * (d : ℝ) * alpha - round (4 * (d : ℝ) * alpha)|
      ∧ 1 / (2 * (q : ℝ)) ≤ |Real.sin (2 * Real.pi * (d : ℝ) * alpha)| := by
  have hqR : (0 : ℝ) < (q : ℝ) := by positivity
  have hqR2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
  have hdq : 2 * (d : ℝ) ≤ (q : ℝ) := by exact_mod_cast hd2
  -- `q` does not divide `a * d`
  have hndvd : ¬ (q : ℤ) ∣ (a * (d : ℤ)) := by
    intro hdvd
    have hcop : IsCoprime ((q : ℤ)) a := by
      rw [Int.isCoprime_iff_gcd_eq_one]
      simpa [Int.gcd, Int.natAbs_natCast] using (Nat.Coprime.symm haq)
    have : (q : ℤ) ∣ (d : ℤ) := hcop.dvd_of_dvd_mul_left hdvd
    have hle : (q : ℕ) ≤ d := Nat.le_of_dvd (by omega) (by exact_mod_cast this)
    omega
  -- the rational part is far from the integers
  have hfrac : 1 / (q : ℝ) ≤ |((a * (d : ℤ) : ℤ) : ℝ) / q - round (((a * (d : ℤ) : ℤ) : ℝ) / q)| :=
    dist_int_fraction (by omega) hndvd
  -- the perturbation is small
  have hpert : |(d : ℝ) * beta| ≤ 1 / (2 * (q : ℝ)) := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (d:ℝ))]
    have h1 : |beta| ≤ 1 / (q : ℝ) ^ 2 := hbeta
    have h2 : (d : ℝ) ≤ (q : ℝ) / 2 := by linarith
    calc (d : ℝ) * |beta| ≤ ((q : ℝ) / 2) * (1 / (q : ℝ) ^ 2) := by
          apply mul_le_mul h2 h1 (abs_nonneg _) (by positivity)
      _ = 1 / (2 * (q : ℝ)) := by field_simp
  have hsplit : 4 * (d : ℝ) * alpha
      = ((a * (d : ℤ) : ℤ) : ℝ) / q + (d : ℝ) * beta := by
    have h1 : ((a * (d : ℤ) : ℤ) : ℝ) / q = (d : ℝ) * ((a : ℝ) / q) := by push_cast; ring
    rw [h1, ← mul_add, ← halpha]
    ring
  have hmain : 1 / (2 * (q : ℝ)) ≤ |4 * (d : ℝ) * alpha - round (4 * (d : ℝ) * alpha)| := by
    rw [hsplit]
    have := dist_int_sub (((a * (d : ℤ) : ℤ) : ℝ) / q) ((d : ℝ) * beta)
    have hq2 : 1 / (q : ℝ) - 1 / (2 * (q : ℝ)) = 1 / (2 * (q : ℝ)) := by
      field_simp
      ring
    linarith [hfrac, hpert, this]
  refine ⟨hmain, ?_⟩
  -- and hence the sine is bounded below
  have hhalf : 1 / (4 * (q : ℝ)) ≤ |2 * (d : ℝ) * alpha - round (2 * (d : ℝ) * alpha)| := by
    have h := dist_int_two_mul (2 * (d : ℝ) * alpha)
    have heq : 2 * (2 * (d : ℝ) * alpha) = 4 * (d : ℝ) * alpha := by ring
    rw [heq] at h
    have hE : (1:ℝ) / (2 * (q : ℝ)) = 2 * (1 / (4 * (q : ℝ))) := by
      field_simp
      ring
    linarith [hmain, hE]
  have h21 := (TaoFivePrimes.two_norm_le_abs_sin_le_pi_norm (2 * (d : ℝ) * alpha)).1
  have heq2 : Real.pi * (2 * (d : ℝ) * alpha) = 2 * Real.pi * (d : ℝ) * alpha := by ring
  rw [heq2] at h21
  have hE2 : (1:ℝ) / (2 * (q : ℝ)) = 2 * (1 / (4 * (q : ℝ))) := by
    field_simp
    ring
  linarith [h21, hhalf, hE2]

end TaoS5
end PartS5

theorem solution
    (alpha beta : ℝ) (a : ℤ) (q : ℕ) (hq : 2 ≤ q)
    (haq : Nat.Coprime a.natAbs q)
    (halpha : 4 * alpha = (a : ℝ) / q + beta)
    (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2)
    (d : ℕ) (hd1 : 1 ≤ d) (hd2 : 2 * d ≤ q) :
    1 / (2 * (q : ℝ)) ≤ |4 * (d : ℝ) * alpha - round (4 * (d : ℝ) * alpha)|
      ∧ 1 / (2 * (q : ℝ)) ≤ |Real.sin (2 * Real.pi * (d : ℝ) * alpha)| :=
  TaoS5.sin_lower_small_d alpha beta a q hq haq halpha hbeta d hd1 hd2
