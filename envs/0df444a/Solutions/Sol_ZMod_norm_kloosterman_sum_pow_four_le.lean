-- Prove2me | solution 1 for ZMod.norm_kloosterman_sum_pow_four_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-13T23:40:34.686367+00:00
-- url     : https://prove2.me/submissions/2d0831ea-589c-4bba-8e82-3dc7cc479a03

import Mathlib
import Definitions.Def_RPLib_S3_KloostermanA

set_option autoImplicit false

theorem solution (p : ℕ) [Fact p.Prime] {m r : ZMod p}
    (hm : m ≠ 0) (hr : r ≠ 0) :
    ‖∑ x : (ZMod p)ˣ, ZMod.stdAddChar (m * (x : ZMod p) + r * (x : ZMod p)⁻¹)‖ ^ 4 ≤
      3 * (p : ℝ) ^ 3 := by
  exact RamanujanPetersson.KL.norm_kl_pow_four_le hm hr
