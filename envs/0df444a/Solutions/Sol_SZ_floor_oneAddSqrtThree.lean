-- Prove2me | solution 1 for SZ.floor_oneAddSqrtThree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:54:10.64595+00:00
-- url     : https://prove2.me/submissions/b4ab7d28-515e-43be-88e5-a5087e7b59f9

import Definitions.Def_SZ_PellDesign
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Definitions.Def_SZ_QuadThm6
import Theorems.Thm_SZ_sqrtThree_pair
import Theorems.Thm_SZ_strace_emod
import Theorems.Thm_SZ_strace_real
import Theorems.Thm_SZ_Pair_abs_pow_le

section
namespace SZ
open Real
private theorem conj_pow_lt (n : ℕ) : (1 - Real.sqrt 3) ^ n ≤ 1 := by
  have h := abs_le.mp (sqrtThree_pair.abs_pow_le n)
  exact h.2
private theorem neg_one_lt_conj_pow (n : ℕ) : -1 < (1 - Real.sqrt 3) ^ n := by
  cases n with
  | zero => norm_num
  | succ k =>
    have h1 : |(1 - Real.sqrt 3) ^ (k + 1)| = |1 - Real.sqrt 3| ^ (k + 1) := abs_pow _ _
    have h2 : |1 - Real.sqrt 3| ^ (k + 1) < 1 :=
      pow_lt_one₀ (abs_nonneg _) sqrtThree_pair.absLt (Nat.succ_ne_zero k)
    have h3 : |(1 - Real.sqrt 3) ^ (k + 1)| < 1 := by rw [h1]; exact h2
    linarith [(abs_lt.mp h3).1]
end SZ
end

set_option autoImplicit false
open SZ
open Real
namespace SZ
theorem _root_.solution (n : ℕ) :
    3 * ⌊(1 / 3 : ℝ) * (1 + Real.sqrt 3) ^ n⌋ = rec2 2 2 2 2 n - 2 := by
  obtain ⟨m, hm⟩ : (6 : ℤ) ∣ (rec2 2 2 2 2 n - 2) := by
    have := strace_emod n; omega
  have hfl : ⌊(1 / 3 : ℝ) * (1 + Real.sqrt 3) ^ n⌋ = 2 * m := by
    have hval : (1 / 3 : ℝ) * (1 + Real.sqrt 3) ^ n
        = (2 * m : ℤ) + (2 - (1 - Real.sqrt 3) ^ n) / 3 := by
      have h := strace_real n
      have hc : ((rec2 2 2 2 2 n : ℤ) : ℝ) = 6 * (m : ℝ) + 2 := by
        have : (rec2 2 2 2 2 n : ℤ) = 6 * m + 2 := by omega
        rw [this]; push_cast; ring
      push_cast
      linarith [h, hc]
    rw [Int.floor_eq_iff, hval]
    have h1 := conj_pow_lt n
    have h2 := neg_one_lt_conj_pow n
    push_cast
    constructor <;> linarith
  rw [hfl]; omega
end SZ
