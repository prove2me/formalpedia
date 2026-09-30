-- Prove2me | solution 1 for ShorAlgorithms.OrderFinding.fraction_unique
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:00:21.923484+00:00
-- url     : https://prove2.me/submissions/5e4f3635-f540-4fa1-a10e-34ad4808e03d

import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic
set_option autoImplicit false

theorem solution (n q c : ℕ) (hnq : n ^ 2 ≤ q) (s₁ s₂ : ℚ)
    (h₁ : s₁.den < n) (h₂ : s₂.den < n)
    (hs₁ : |(c : ℚ) / q - s₁| ≤ 1 / (2 * q)) (hs₂ : |(c : ℚ) / q - s₂| ≤ 1 / (2 * q)) :
    s₁ = s₂ := by
  have hd₁ : (0 : ℚ) < s₁.den := by exact_mod_cast s₁.pos
  have hd₂ : (0 : ℚ) < s₂.den := by exact_mod_cast s₂.pos
  have hd₁n : (s₁.den : ℚ) < n := by exact_mod_cast h₁
  have hd₂n : (s₂.den : ℚ) < n := by exact_mod_cast h₂
  have hnq' : (n : ℚ)^2 ≤ q := by exact_mod_cast hnq
  have hprod : (s₁.den : ℚ) * s₂.den < q := by nlinarith
  have hq : (0 : ℚ) < q := lt_trans (mul_pos hd₁ hd₂) hprod
  have hdist : |s₁-s₂| ≤ 1/(q : ℚ) := by
    calc
      |s₁-s₂| = |((c : ℚ)/q-s₂)-((c : ℚ)/q-s₁)| := by congr 1; ring
      _ ≤ |(c : ℚ)/q-s₂|+|(c : ℚ)/q-s₁| := abs_sub _ _
      _ ≤ 1/(2*(q : ℚ))+1/(2*(q : ℚ)) := add_le_add hs₂ hs₁
      _ = 1/(q : ℚ) := by ring
  have hsmall : |s₁-s₂| * ((s₁.den : ℚ)*s₂.den) < 1 := by
    apply lt_of_le_of_lt (mul_le_mul_of_nonneg_right hdist (mul_pos hd₁ hd₂).le)
    rw [one_div_mul_eq_div]
    exact (div_lt_one hq).mpr hprod
  have hident : (s₁-s₂)*((s₁.den : ℚ)*s₂.den) =
      ((s₁.num*(s₂.den : ℤ)-s₂.num*(s₁.den : ℤ) : ℤ) : ℚ) := by
    push_cast
    have hx := Rat.mul_den_eq_num s₁
    have hy := Rat.mul_den_eq_num s₂
    nlinarith
  have hint : |s₁.num*(s₂.den : ℤ)-s₂.num*(s₁.den : ℤ)| < 1 := by
    have hh : |((s₁.num*(s₂.den : ℤ)-s₂.num*(s₁.den : ℤ) : ℤ) : ℚ)| < 1 := by
      rw [← hident, abs_mul, abs_of_pos (mul_pos hd₁ hd₂)]
      exact hsmall
    exact_mod_cast hh
  apply Rat.eq_iff_mul_eq_mul.mpr
  have hzero : s₁.num*(s₂.den : ℤ)-s₂.num*(s₁.den : ℤ) = 0 := by
    obtain ⟨hlo, hhi⟩ := abs_lt.mp hint
    omega
  exact sub_eq_zero.mp hzero
