-- Prove2me | solution 1 for SZ.Slice.eq_fixed_of_trapped
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:26:48.496364+00:00
-- url     : https://prove2.me/submissions/c446fce6-5a9f-4e94-b471-b068d54e05a8

import Definitions.Def_SZ_Slice
import Mathlib.Tactic.Push
import Definitions.Def_SZ_SliceHygiene

set_option autoImplicit false
open SZ
open SZ.Slice
namespace SZ.Slice
theorem _root_.solution {f : ℕ → ℝ} {r c D : ℝ} {K : ℕ} (hr : 1 < r)
    (hrec : ∀ k, K ≤ k → f (k + 1) = r * f k - c)
    (hbd : ∀ k, K ≤ k → |f k - c / (r - 1)| ≤ D) : f K = c / (r - 1) := by
  by_contra hne
  have hr1 : (0 : ℝ) < r - 1 := by linarith
  have hpos : 0 < |f K - c / (r - 1)| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hpow : ∀ n : ℕ, f (K + n) - c / (r - 1) = r ^ n * (f K - c / (r - 1)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hstep := hrec (K + n) (Nat.le_add_right _ _)
      have e : K + (n + 1) = (K + n) + 1 := by omega
      rw [e, hstep, pow_succ]
      have hc : r * (c / (r - 1)) - c = c / (r - 1) := by field_simp; ring
      nlinarith [ih]
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (D / |f K - c / (r - 1)|) hr
  have hb := hbd (K + n) (Nat.le_add_right _ _)
  rw [hpow n, abs_mul, abs_pow, abs_of_nonneg (by linarith : (0:ℝ) ≤ r)] at hb
  have hlt := (div_lt_iff₀ hpos).mp hn
  nlinarith [hpos]
end SZ.Slice
