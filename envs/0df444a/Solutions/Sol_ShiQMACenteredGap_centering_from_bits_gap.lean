-- Prove2me | solution 1 for ShiQMACenteredGap.centering_from_bits_gap
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-10-01T11:54:17.794378+00:00
-- url     : https://prove2.me/submissions/1c4445a8-d62b-4263-9dac-f460823b3530

import Definitions.Def_ShiQMACenteredGapComputableCoin
import Theorems.Thm_ShiQMACenteredGap_centering_from_bits
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false

open ShiQMACenteredGap

theorem solution {a b : ℝ} (hab : b ≤ a)
    (q : Nat) (hgap : (1 : ℝ) ≤ (q : ℝ) * (a - b))
    (as bs : List Bool) (haLen : as.length = coinBits q) (hbLen : bs.length = coinBits q)
    (ha : |dyadicValue as - a| ≤ 1 / (2 : ℝ) ^ coinBits q)
    (hb : |dyadicValue bs - b| ≤ 1 / (2 : ℝ) ^ coinBits q) :
    let j := centeringNumerator (coinBits q) (binaryNumerator as) (binaryNumerator bs)
    j ≤ 2 ^ (coinBits q + 1) ∧
      |(j : ℝ) / (2 : ℝ) ^ (coinBits q + 1) - centeringCoin a b| ≤ (a - b) / 4 := by
  refine ⟨centeringNumerator_le _ _ _, ?_⟩
  have herr := centering_from_bits as bs (haLen.trans hbLen.symm)
    (by simpa [haLen] using ha) (by simpa [haLen] using hb)
  rw [haLen] at herr
  apply herr.trans
  have hpos : (0 : ℝ) < 2 ^ coinBits q := pow_pos (by norm_num) _
  have hnat : 4 * q ≤ 2 ^ coinBits q :=
    Nat.le_of_lt (Nat.lt_pow_succ_log_self (by decide : 1 < 2) (4 * q))
  have hreal : 4 * (q : ℝ) ≤ (2 : ℝ) ^ coinBits q := by exact_mod_cast hnat
  apply (div_le_iff₀ hpos).mpr
  have hm := mul_nonneg (sub_nonneg.mpr hreal) (sub_nonneg.mpr hab)
  nlinarith
