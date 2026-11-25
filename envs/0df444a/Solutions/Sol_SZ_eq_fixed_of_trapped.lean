-- Prove2me | solution 1 for SZ.eq_fixed_of_trapped
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:57:03.95507+00:00
-- url     : https://prove2.me/submissions/a1979310-602e-4bf3-99e8-03bf3f4e2194

import Definitions.Def_SZ_DigitParity
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_SZ_CoverGame

set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution {f : ℕ → ℝ} {c D : ℝ} {K : ℕ}
    (hrec : ∀ k, K ≤ k → f (k + 1) = 3 * f k - c)
    (hbd : ∀ k, K ≤ k → |f k - c / 2| ≤ D) : f K = c / 2 := by
  by_contra hne
  have hpos : 0 < |f K - c / 2| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hpow : ∀ j : ℕ, f (K + j) - c / 2 = 3 ^ j * (f K - c / 2) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hstep := hrec (K + j) (Nat.le_add_right _ _)
      have e : K + (j + 1) = (K + j) + 1 := by omega
      rw [e, hstep, pow_succ]
      linarith
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (D / |f K - c / 2|) (by norm_num : (1:ℝ) < 3)
  have hb := hbd (K + n) (Nat.le_add_right _ _)
  rw [hpow n, abs_mul, abs_pow, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 3)] at hb
  have hlt := (div_lt_iff₀ hpos).mp hn
  linarith
end SZ
