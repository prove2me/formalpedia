-- Prove2me | solution 1 for ShiQMACenteredGap.biasIter_dyadic
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-10-01T01:00:05.6644+00:00
-- url     : https://prove2.me/submissions/d8b4a977-177a-44b6-a0ad-e2a5f04c4ea7

import Definitions.Def_ShiQMACenteredGap
import Theorems.Thm_ShiQMACenteredGap_biasIter_growth

set_option autoImplicit false
open ShiQMACenteredGap

theorem solution {d : ℝ} (hd : 0 ≤ d) (hd' : d ≤ 1 / 2) (r : Nat) :
    min (1 / 6) ((2 : ℝ) ^ r * d) ≤ biasIter d (3 * r) := by
  have hp : (2 : ℝ) ^ r ≤ ((4 : ℝ) / 3) ^ (3 * r) := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) r
  exact (min_le_min_left _ (mul_le_mul_of_nonneg_right hp hd)).trans
    (biasIter_growth hd hd' (3 * r))
