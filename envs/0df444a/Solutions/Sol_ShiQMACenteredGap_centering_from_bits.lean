-- Prove2me | solution 1 for ShiQMACenteredGap.centering_from_bits
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-10-01T11:39:05.754811+00:00
-- url     : https://prove2.me/submissions/694de36c-9b42-4808-aad7-b2542f31a767

import Definitions.Def_ShiQMACenteredGapComputableCoin
import Theorems.Thm_ShiQMACenteredGap_centeringNumerator_value
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false

open ShiQMACenteredGap

theorem solution {a b : ℝ} (as bs : List Bool) (hlen : as.length = bs.length)
    (ha : |dyadicValue as - a| ≤ 1 / (2 : ℝ) ^ as.length)
    (hb : |dyadicValue bs - b| ≤ 1 / (2 : ℝ) ^ as.length) :
    let j := centeringNumerator as.length (binaryNumerator as) (binaryNumerator bs)
    |(j : ℝ) / (2 : ℝ) ^ (as.length + 1) - centeringCoin a b| ≤
      1 / (2 : ℝ) ^ as.length := by
  dsimp only
  have hB : binaryNumerator bs ≤ 2 ^ as.length := by
    rw [hlen]
    exact (binaryNumerator_lt bs).le
  rw [centeringNumerator_value _ _ _ (binaryNumerator_lt as).le hB]
  have he : (binaryNumerator bs : ℝ) / (2 : ℝ) ^ as.length = dyadicValue bs := by
    rw [hlen]; rfl
  change |1 - (dyadicValue as + (binaryNumerator bs : ℝ) / (2 : ℝ) ^ as.length) / 2 -
    centeringCoin a b| ≤ _
  rw [he]
  obtain ⟨hal, har⟩ := abs_le.mp ha
  obtain ⟨hbl, hbr⟩ := abs_le.mp hb
  apply abs_le.mpr
  dsimp [centeringCoin]
  constructor <;> linarith
