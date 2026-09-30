-- Prove2me | solution 1 for ShiQMACenteredGap.biasIter_gapRounds
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-30T07:14:28.344809+00:00
-- url     : https://prove2.me/submissions/4ca13081-9c94-4a23-bc6c-db3d79b2a147

import Definitions.Def_ShiQMACenteredGap
import Theorems.Thm_ShiQMACenteredGap_biasIter_growth

set_option autoImplicit false
open ShiQMAErrorIteration ShiQMACenteredGap

/-- Three rounds suffice for each factor of two in the initial inverse bias. -/
private theorem biasIter_dyadic {d : ℝ} (hd : 0 ≤ d) (hd' : d ≤ 1 / 2) (r : Nat) :
    min (1 / 6) ((2 : ℝ) ^ r * d) ≤ biasIter d (3 * r) := by
  have hp : (2 : ℝ) ^ r ≤ ((4 : ℝ) / 3) ^ (3 * r) := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) r
  exact (min_le_min_left _ (mul_le_mul_of_nonneg_right hp hd)).trans
    (biasIter_growth hd hd' (3 * r))

theorem solution {d : ℝ} (hd : 0 ≤ d) (hd' : d ≤ 1 / 2)
    (q : Nat) (hgap : (1 / 6 : ℝ) ≤ (q : ℝ) * d) :
    (1 / 6 : ℝ) ≤ biasIter d (gapRounds q) := by
  have hq : q ≤ 2 ^ (Nat.log 2 q + 1) :=
    Nat.le_of_lt (Nat.lt_pow_succ_log_self (by decide : 1 < 2) q)
  have hqr : (q : ℝ) ≤ (2 : ℝ) ^ (Nat.log 2 q + 1) := by exact_mod_cast hq
  have h := biasIter_dyadic hd hd' (Nat.log 2 q + 1)
  rw [min_eq_left (hgap.trans (mul_le_mul_of_nonneg_right hqr hd))] at h
  exact h
