-- Prove2me | solution 1 for ShiQMACenteredGap.exists_dyadic_centering
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-10-01T09:42:58.715367+00:00
-- url     : https://prove2.me/submissions/b589c2d2-b8ac-4ab4-ac1c-1f7a0b142b1e

import Definitions.Def_ShiQMACenteredGapScalarCentering
import Theorems.Thm_ShiQMACenteredGap_exists_dyadic_coin
import Mathlib.Tactic
import Mathlib.Data.Real.Archimedean

set_option autoImplicit false

open ShiQMACenteredGap

private theorem centeringCoin_bounds {a b : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1)
    (hb₀ : 0 ≤ b) (hb₁ : b ≤ 1) :
    0 ≤ centeringCoin a b ∧ centeringCoin a b ≤ 1 := by
  dsimp [centeringCoin]
  constructor <;> linarith

theorem solution {a b : ℝ}
    (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1) (hb₀ : 0 ≤ b) (hb₁ : b ≤ 1)
    (hab : b ≤ a) (q : Nat) (hgap : (1 : ℝ) ≤ (q : ℝ) * (a - b)) :
    ∃ j : Nat, j ≤ 2 ^ coinBits q ∧
      |(j : ℝ) / (2 : ℝ) ^ coinBits q - centeringCoin a b| ≤ (a - b) / 4 := by
  obtain ⟨hu₀, hu₁⟩ := centeringCoin_bounds ha₀ ha₁ hb₀ hb₁
  obtain ⟨j, hj, herr⟩ := exists_dyadic_coin hu₀ hu₁ (coinBits q)
  refine ⟨j, hj, herr.le.trans ?_⟩
  have hN : (0 : ℝ) < 2 ^ coinBits q := pow_pos (by norm_num) _
  have hnat : 4 * q ≤ 2 ^ coinBits q :=
    Nat.le_of_lt (Nat.lt_pow_succ_log_self (by decide : 1 < 2) (4 * q))
  have hreal : 4 * (q : ℝ) ≤ (2 : ℝ) ^ coinBits q := by exact_mod_cast hnat
  apply (div_le_iff₀ hN).mpr
  have hmul := mul_nonneg (sub_nonneg.mpr hreal) (sub_nonneg.mpr hab)
  nlinarith
