-- Prove2me | solution 1 for PlatformEntry.Regimes.proposition2_receptive_regime
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T10:26:39.447644+00:00
-- url     : https://prove2.me/submissions/ca69c269-5aa0-4241-9bdd-a3ec9080be6e

import Mathlib
import Definitions.Def_PlatformEntry_Regimes_Model

set_option autoImplicit false

namespace E30B5F0B

open PlatformEntry.Regimes

/-! ## Polynomial facts on the box -/

lemma ft_poly (d f b : ℝ) (hd0 : 0 ≤ d) (hd1 : 0 ≤ 1 - d) (hf0 : 0 ≤ f) (hf1 : 0 ≤ 1 - f)
    (hb0 : 0 ≤ b) (hb1 : 0 ≤ 1 - b) :
    2 ≤ (- 4 * d ^ 2 * f ^ 2 + 4 * d ^ 2 + 12 * d * f ^ 2 * b + 12 * d * f * b - 4 * d * f - 12 * f ^ 2 * b ^ 2 - 24 * f * b ^ 2 + 12 * f * b + 8 * f - 12 * b ^ 2 + 12 * b + 8) + 5 / 2 * b * (- 4 * d ^ 2 * f ^ 2 * b + 4 * d ^ 2 * b - 4 * d ^ 2 + 6 * d * f ^ 2 * b ^ 2 + 6 * d * f * b ^ 2 - 4 * d * f * b - 8 * d * f - 4 * d - 4 * f ^ 2 * b ^ 3 - 8 * f * b ^ 3 + 6 * f * b ^ 2 + 8 * f * b - 4 * b ^ 3 + 6 * b ^ 2 + 8 * b - 8) := by
  linarith [mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hd0 0) (pow_nonneg hd1 2)) (mul_nonneg (pow_nonneg hf0 0) (pow_nonneg hf1 2))) (mul_nonneg (pow_nonneg hb0 0) (pow_nonneg hb1 6)),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hd0 0) (pow_nonneg hd1 2)) (mul_nonneg (pow_nonneg hf0 0) (pow_nonneg hf1 2))) (mul_nonneg (pow_nonneg hb0 1) (pow_nonneg hb1 5)),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hd0 0) (pow_nonneg hd1 2)) (mul_nonneg (pow_nonneg hf0 0) (pow_nonneg hf1 2))) (mul_nonneg (pow_nonneg hb0 2) (pow_nonneg hb1 4)),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hd0 0) (pow_nonneg hd1 2)) (mul_nonneg (pow_nonneg hf0 0) (pow_nonneg hf1 2))) (mul_nonneg (pow_nonneg hb0 3) (pow_nonneg hb1 3)),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hd0 0) (pow_nonneg hd1 2)) (mul_nonneg (pow_nonneg hf0 0) (pow_nonneg hf1 2))) (mul_nonneg (pow_nonneg hb0 4) (pow_nonneg hb1 2)),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hd0 0) (pow_nonneg hd1 2)) (mul_nonneg (pow_nonneg hf0 0) (pow_nonneg hf1 2))) (mul_nonneg (pow_nonneg hb0 5) (pow_nonneg hb1 1)),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hd0 0) (pow_nonneg hd1 2)) (mul_nonneg (pow_nonneg hf0 0) (pow_nonneg hf1 2))) (mul_nonneg (pow_nonneg hb0 6) (pow_nonneg hb1 0)),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hd0 0) (pow_nonneg hd1 2)) (mul_nonneg (pow_nonneg hf0 1) (pow_nonneg hf1 1))) (mul_nonneg (pow_nonneg hb0 0) (pow_nonneg hb1 6)),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hd0 0) (pow_nonneg hd1 2)) (mul_nonneg (pow_nonneg hf0 1) (pow_nonneg hf1 1))) (mul_nonneg (pow_nonneg hb0 1) (pow_nonneg hb1 5)),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hd0 0) (pow_nonneg hd1 2)) (mul_nonneg (pow_nonneg hf0 1) (pow_nonneg hf1 1))) (mul_nonneg (pow_nonneg hb0 2) (pow_nonneg hb1 4)),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hd0 0) (pow_nonneg hd1 2)) (mul_nonneg (pow_nonneg hf0 1) (pow_nonneg hf1 1))) (mul_nonneg (pow_nonneg hb0 3) (pow_nonneg hb1 3)),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hd0 0) (pow_nonneg hd1 2)) (mul_nonneg (pow_nonneg hf0 1) (pow_nonneg hf1 1))) (mul_nonneg (pow_nonneg hb0 4) (pow_nonneg hb1 2)),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hd0 0) (pow_nonneg hd1 2)) (mul_nonneg (pow_nonneg hf0 1) (pow_nonneg hf1 1))) (mul_nonneg (pow_nonneg hb0 5) (pow_nonneg hb1 1)),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hd0 0) (pow_nonneg hd1 2)) (mul_nonneg (pow_nonneg hf0 1) (pow_nonneg hf1 1))) (mul_nonneg (pow_nonneg hb0 6) (pow_nonneg hb1 0)),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hd0 0) (pow_nonneg hd1 2)) (mul_nonneg (pow_nonneg hf0 2) (pow_nonneg hf1 0))) (mul_nonneg (pow_nonneg hb0 0) (pow_nonneg hb1 6)),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hd0 0) (pow_nonneg hd1 2)) (mul_nonneg (pow_nonneg hf0 2) (pow_nonneg hf1 0))) (mul_nonneg (pow_nonneg hb0 1) (pow_nonneg hb1 5)),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hd0 0) (pow_nonneg hd1 2)) (mul_nonneg (pow_nonneg hf0 2) (pow_nonneg hf1 0))) (mul_nonneg (pow_nonneg hb0 2) (pow_nonneg hb1 4)),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hd0 0) (pow_nonneg hd1 2)) (mul_nonneg (pow_nonneg hf0 2) (pow_nonneg hf1 0))) (mul_nonneg (pow_nonneg hb0 3) (pow_nonneg hb1 3)),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hd0 0) (pow_nonneg hd1 2)) (mul_nonneg (pow_nonneg hf0 2) (pow_nonneg hf1 0))) (mul_nonneg (pow_nonneg hb0 4) (pow_nonneg hb1 2)),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hd0 0) (pow_nonneg hd1 2)) (mul_nonneg (pow_nonneg hf0 2) (pow_nonneg hf1 0))) (mul_nonneg (pow_nonneg hb0 5) (pow_nonneg hb1 1)),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hd0 1) (pow_nonneg hd1 1)) (mul_nonneg (pow_nonneg hf0 0) (pow_nonneg hf1 2))) (mul_nonneg (pow_nonneg hb0 0) (pow_nonneg hb1 6)),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hd0 1) (pow_nonneg hd1 1)) (mul_nonneg (pow_nonneg hf0 0) (pow_nonneg hf1 2))) (mul_nonneg (pow_nonneg hb0 1) (pow_nonneg hb1 5)),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hd0 1) (pow_nonneg hd1 1)) (mul_nonneg (pow_nonneg hf0 0) (pow_nonneg hf1 2))) (mul_nonneg (pow_nonneg hb0 2) (pow_nonneg hb1 4)),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hd0 1) (pow_nonneg hd1 1)) (mul_nonneg (pow_nonneg hf0 0) (pow_nonneg hf1 2))) (mul_nonneg (pow_nonneg hb0 3) (pow_nonneg hb1 3)),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hd0 1) (pow_nonneg hd1 1)) (mul_nonneg (pow_nonneg hf0 0) (pow_nonneg hf1 2))) (mul_nonneg (pow_nonneg hb0 4) (pow_nonneg hb1 2)),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hd0 1) (pow_nonneg hd1 1)) (mul_nonneg (pow_nonneg hf0 0) (pow_nonneg hf1 2))) (mul_nonneg (pow_nonneg hb0 5) (pow_nonneg hb1 1)),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hd0 1) (pow_nonneg hd1 1)) (mul_nonneg (pow_nonneg hf0 0) (pow_nonneg hf1 2))) (mul_nonneg (pow_nonneg hb0 6) (pow_nonneg hb1 0)),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hd0 1) (pow_nonneg hd1 1)) (mul_nonneg (pow_nonneg hf0 1) (pow_nonneg hf1 1))) (mul_nonneg (pow_nonneg hb0 0) (pow_nonneg hb1 6)),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hd0 1) (pow_nonneg hd1 1)) (mul_nonneg (pow_nonneg hf0 1) (pow_nonneg hf1 1))) (mul_nonneg (pow_nonneg hb0 1) (pow_nonneg hb1 5)),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hd0 1) (pow_nonneg hd1 1)) (mul_nonneg (pow_nonneg hf0 1) (pow_nonneg hf1 1))) (mul_nonneg (pow_nonneg hb0 2) (pow_nonneg hb1 4)),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hd0 1) (pow_nonneg hd1 1)) (mul_nonneg (pow_nonneg hf0 1) (pow_nonneg hf1 1))) (mul_nonneg (pow_nonneg hb0 3) (pow_nonneg hb1 3)),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hd0 1) (pow_nonneg hd1 1)) (mul_nonneg (pow_nonneg hf0 1) (pow_nonneg hf1 1))) (mul_nonneg (pow_nonneg hb0 4) (pow_nonneg hb1 2)),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hd0 1) (pow_nonneg hd1 1)) (mul_nonneg (pow_nonneg hf0 1) (pow_nonneg hf1 1))) (mul_nonneg (pow_nonneg hb0 5) (pow_nonneg hb1 1)),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hd0 1) (pow_nonneg hd1 1)) (mul_nonneg (pow_nonneg hf0 1) (pow_nonneg hf1 1))) (mul_nonneg (pow_nonneg hb0 6) (pow_nonneg hb1 0)),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hd0 1) (pow_nonneg hd1 1)) (mul_nonneg (pow_nonneg hf0 2) (pow_nonneg hf1 0))) (mul_nonneg (pow_nonneg hb0 0) (pow_nonneg hb1 6)),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hd0 1) (pow_nonneg hd1 1)) (mul_nonneg (pow_nonneg hf0 2) (pow_nonneg hf1 0))) (mul_nonneg (pow_nonneg hb0 1) (pow_nonneg hb1 5)),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hd0 1) (pow_nonneg hd1 1)) (mul_nonneg (pow_nonneg hf0 2) (pow_nonneg hf1 0))) (mul_nonneg (pow_nonneg hb0 2) (pow_nonneg hb1 4)),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hd0 1) (pow_nonneg hd1 1)) (mul_nonneg (pow_nonneg hf0 2) (pow_nonneg hf1 0))) (mul_nonneg (pow_nonneg hb0 3) (pow_nonneg hb1 3)),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hd0 1) (pow_nonneg hd1 1)) (mul_nonneg (pow_nonneg hf0 2) (pow_nonneg hf1 0))) (mul_nonneg (pow_nonneg hb0 4) (pow_nonneg hb1 2)),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hd0 1) (pow_nonneg hd1 1)) (mul_nonneg (pow_nonneg hf0 2) (pow_nonneg hf1 0))) (mul_nonneg (pow_nonneg hb0 5) (pow_nonneg hb1 1)),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hd0 1) (pow_nonneg hd1 1)) (mul_nonneg (pow_nonneg hf0 2) (pow_nonneg hf1 0))) (mul_nonneg (pow_nonneg hb0 6) (pow_nonneg hb1 0)),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hd0 2) (pow_nonneg hd1 0)) (mul_nonneg (pow_nonneg hf0 0) (pow_nonneg hf1 2))) (mul_nonneg (pow_nonneg hb0 0) (pow_nonneg hb1 6)),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hd0 2) (pow_nonneg hd1 0)) (mul_nonneg (pow_nonneg hf0 0) (pow_nonneg hf1 2))) (mul_nonneg (pow_nonneg hb0 1) (pow_nonneg hb1 5)),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hd0 2) (pow_nonneg hd1 0)) (mul_nonneg (pow_nonneg hf0 0) (pow_nonneg hf1 2))) (mul_nonneg (pow_nonneg hb0 2) (pow_nonneg hb1 4)),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hd0 2) (pow_nonneg hd1 0)) (mul_nonneg (pow_nonneg hf0 0) (pow_nonneg hf1 2))) (mul_nonneg (pow_nonneg hb0 3) (pow_nonneg hb1 3)),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hd0 2) (pow_nonneg hd1 0)) (mul_nonneg (pow_nonneg hf0 0) (pow_nonneg hf1 2))) (mul_nonneg (pow_nonneg hb0 4) (pow_nonneg hb1 2)),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hd0 2) (pow_nonneg hd1 0)) (mul_nonneg (pow_nonneg hf0 0) (pow_nonneg hf1 2))) (mul_nonneg (pow_nonneg hb0 5) (pow_nonneg hb1 1)),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hd0 2) (pow_nonneg hd1 0)) (mul_nonneg (pow_nonneg hf0 0) (pow_nonneg hf1 2))) (mul_nonneg (pow_nonneg hb0 6) (pow_nonneg hb1 0)),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hd0 2) (pow_nonneg hd1 0)) (mul_nonneg (pow_nonneg hf0 1) (pow_nonneg hf1 1))) (mul_nonneg (pow_nonneg hb0 0) (pow_nonneg hb1 6)),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hd0 2) (pow_nonneg hd1 0)) (mul_nonneg (pow_nonneg hf0 1) (pow_nonneg hf1 1))) (mul_nonneg (pow_nonneg hb0 1) (pow_nonneg hb1 5)),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hd0 2) (pow_nonneg hd1 0)) (mul_nonneg (pow_nonneg hf0 1) (pow_nonneg hf1 1))) (mul_nonneg (pow_nonneg hb0 2) (pow_nonneg hb1 4)),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hd0 2) (pow_nonneg hd1 0)) (mul_nonneg (pow_nonneg hf0 1) (pow_nonneg hf1 1))) (mul_nonneg (pow_nonneg hb0 3) (pow_nonneg hb1 3)),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hd0 2) (pow_nonneg hd1 0)) (mul_nonneg (pow_nonneg hf0 1) (pow_nonneg hf1 1))) (mul_nonneg (pow_nonneg hb0 4) (pow_nonneg hb1 2)),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hd0 2) (pow_nonneg hd1 0)) (mul_nonneg (pow_nonneg hf0 1) (pow_nonneg hf1 1))) (mul_nonneg (pow_nonneg hb0 5) (pow_nonneg hb1 1)),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hd0 2) (pow_nonneg hd1 0)) (mul_nonneg (pow_nonneg hf0 1) (pow_nonneg hf1 1))) (mul_nonneg (pow_nonneg hb0 6) (pow_nonneg hb1 0)),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hd0 2) (pow_nonneg hd1 0)) (mul_nonneg (pow_nonneg hf0 2) (pow_nonneg hf1 0))) (mul_nonneg (pow_nonneg hb0 0) (pow_nonneg hb1 6)),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hd0 2) (pow_nonneg hd1 0)) (mul_nonneg (pow_nonneg hf0 2) (pow_nonneg hf1 0))) (mul_nonneg (pow_nonneg hb0 1) (pow_nonneg hb1 5)),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hd0 2) (pow_nonneg hd1 0)) (mul_nonneg (pow_nonneg hf0 2) (pow_nonneg hf1 0))) (mul_nonneg (pow_nonneg hb0 2) (pow_nonneg hb1 4)),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hd0 2) (pow_nonneg hd1 0)) (mul_nonneg (pow_nonneg hf0 2) (pow_nonneg hf1 0))) (mul_nonneg (pow_nonneg hb0 3) (pow_nonneg hb1 3)),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hd0 2) (pow_nonneg hd1 0)) (mul_nonneg (pow_nonneg hf0 2) (pow_nonneg hf1 0))) (mul_nonneg (pow_nonneg hb0 4) (pow_nonneg hb1 2)),
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hd0 2) (pow_nonneg hd1 0)) (mul_nonneg (pow_nonneg hf0 2) (pow_nonneg hf1 0))) (mul_nonneg (pow_nonneg hb0 5) (pow_nonneg hb1 1))]

lemma dh_poly (f b : ℝ) (hf0 : 0 ≤ f) (hf1 : 0 ≤ 1 - f) (hb0 : 0 ≤ b) (hb1 : 0 ≤ 1 - b) :
    4 * (1 - f) ≤ (1/2) * f ^ 2 * b ^ 4 + f * b ^ 4 - 4 * f * b ^ 2 + (1/2) * b ^ 4 - 4 * b ^ 2 + 8 := by
  linarith [mul_nonneg (mul_nonneg (pow_nonneg hf0 0) (pow_nonneg hf1 2)) (mul_nonneg (pow_nonneg hb0 0) (pow_nonneg hb1 4)),
    mul_nonneg (mul_nonneg (pow_nonneg hf0 0) (pow_nonneg hf1 2)) (mul_nonneg (pow_nonneg hb0 1) (pow_nonneg hb1 3)),
    mul_nonneg (mul_nonneg (pow_nonneg hf0 0) (pow_nonneg hf1 2)) (mul_nonneg (pow_nonneg hb0 2) (pow_nonneg hb1 2)),
    mul_nonneg (mul_nonneg (pow_nonneg hf0 0) (pow_nonneg hf1 2)) (mul_nonneg (pow_nonneg hb0 3) (pow_nonneg hb1 1)),
    mul_nonneg (mul_nonneg (pow_nonneg hf0 0) (pow_nonneg hf1 2)) (mul_nonneg (pow_nonneg hb0 4) (pow_nonneg hb1 0)),
    mul_nonneg (mul_nonneg (pow_nonneg hf0 1) (pow_nonneg hf1 1)) (mul_nonneg (pow_nonneg hb0 0) (pow_nonneg hb1 4)),
    mul_nonneg (mul_nonneg (pow_nonneg hf0 1) (pow_nonneg hf1 1)) (mul_nonneg (pow_nonneg hb0 1) (pow_nonneg hb1 3)),
    mul_nonneg (mul_nonneg (pow_nonneg hf0 1) (pow_nonneg hf1 1)) (mul_nonneg (pow_nonneg hb0 2) (pow_nonneg hb1 2)),
    mul_nonneg (mul_nonneg (pow_nonneg hf0 1) (pow_nonneg hf1 1)) (mul_nonneg (pow_nonneg hb0 3) (pow_nonneg hb1 1)),
    mul_nonneg (mul_nonneg (pow_nonneg hf0 1) (pow_nonneg hf1 1)) (mul_nonneg (pow_nonneg hb0 4) (pow_nonneg hb1 0)),
    mul_nonneg (mul_nonneg (pow_nonneg hf0 2) (pow_nonneg hf1 0)) (mul_nonneg (pow_nonneg hb0 0) (pow_nonneg hb1 4)),
    mul_nonneg (mul_nonneg (pow_nonneg hf0 2) (pow_nonneg hf1 0)) (mul_nonneg (pow_nonneg hb0 1) (pow_nonneg hb1 3)),
    mul_nonneg (mul_nonneg (pow_nonneg hf0 2) (pow_nonneg hf1 0)) (mul_nonneg (pow_nonneg hb0 2) (pow_nonneg hb1 2)),
    mul_nonneg (mul_nonneg (pow_nonneg hf0 2) (pow_nonneg hf1 0)) (mul_nonneg (pow_nonneg hb0 3) (pow_nonneg hb1 1)),
    mul_nonneg (mul_nonneg (pow_nonneg hf0 2) (pow_nonneg hf1 0)) (mul_nonneg (pow_nonneg hb0 4) (pow_nonneg hb1 0))]

lemma d1_poly (f b : ℝ) (hf0 : 0 ≤ f) (hf1 : 0 ≤ 1 - f) (hb0 : 0 ≤ b) (hb1 : 0 ≤ 1 - b) :
    4 * (1 - f) ≤ f ^ 2 * b ^ 4 - 2 * f ^ 2 * b ^ 3 + 2 * f ^ 2 * b ^ 2 + 2 * f * b ^ 4 - 2 * f * b ^ 3 - 6 * f * b ^ 2 + 8 * f * b - 8 * f + b ^ 4 - 10 * b ^ 2 + 8 * b + 8 := by
  linarith [mul_nonneg (mul_nonneg (pow_nonneg hf0 0) (pow_nonneg hf1 2)) (mul_nonneg (pow_nonneg hb0 0) (pow_nonneg hb1 4)),
    mul_nonneg (mul_nonneg (pow_nonneg hf0 0) (pow_nonneg hf1 2)) (mul_nonneg (pow_nonneg hb0 1) (pow_nonneg hb1 3)),
    mul_nonneg (mul_nonneg (pow_nonneg hf0 0) (pow_nonneg hf1 2)) (mul_nonneg (pow_nonneg hb0 2) (pow_nonneg hb1 2)),
    mul_nonneg (mul_nonneg (pow_nonneg hf0 0) (pow_nonneg hf1 2)) (mul_nonneg (pow_nonneg hb0 3) (pow_nonneg hb1 1)),
    mul_nonneg (mul_nonneg (pow_nonneg hf0 0) (pow_nonneg hf1 2)) (mul_nonneg (pow_nonneg hb0 4) (pow_nonneg hb1 0)),
    mul_nonneg (mul_nonneg (pow_nonneg hf0 1) (pow_nonneg hf1 1)) (mul_nonneg (pow_nonneg hb0 0) (pow_nonneg hb1 4)),
    mul_nonneg (mul_nonneg (pow_nonneg hf0 1) (pow_nonneg hf1 1)) (mul_nonneg (pow_nonneg hb0 1) (pow_nonneg hb1 3)),
    mul_nonneg (mul_nonneg (pow_nonneg hf0 1) (pow_nonneg hf1 1)) (mul_nonneg (pow_nonneg hb0 2) (pow_nonneg hb1 2)),
    mul_nonneg (mul_nonneg (pow_nonneg hf0 1) (pow_nonneg hf1 1)) (mul_nonneg (pow_nonneg hb0 3) (pow_nonneg hb1 1)),
    mul_nonneg (mul_nonneg (pow_nonneg hf0 1) (pow_nonneg hf1 1)) (mul_nonneg (pow_nonneg hb0 4) (pow_nonneg hb1 0)),
    mul_nonneg (mul_nonneg (pow_nonneg hf0 2) (pow_nonneg hf1 0)) (mul_nonneg (pow_nonneg hb0 1) (pow_nonneg hb1 3)),
    mul_nonneg (mul_nonneg (pow_nonneg hf0 2) (pow_nonneg hf1 0)) (mul_nonneg (pow_nonneg hb0 2) (pow_nonneg hb1 2)),
    mul_nonneg (mul_nonneg (pow_nonneg hf0 2) (pow_nonneg hf1 0)) (mul_nonneg (pow_nonneg hb0 3) (pow_nonneg hb1 1)),
    mul_nonneg (mul_nonneg (pow_nonneg hf0 2) (pow_nonneg hf1 0)) (mul_nonneg (pow_nonneg hb0 4) (pow_nonneg hb1 0))]

lemma twoAB (f b : ℝ) (hf0 : 0 ≤ f) (hf1 : f ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    0 ≤ 2 * (8 * f - 4 * b + 2 * b ^ 2 * (1 - f ^ 2)) +
      (8 + 2 * b ^ 3 * f * (1 + f) - 4 * b * (1 + 2 * f) - 2 * b ^ 2 * f) := by
  nlinarith [mul_nonneg hf0 hb0, mul_nonneg (sub_nonneg.2 hf1) (sub_nonneg.2 hb1),
    mul_nonneg hb0 (sub_nonneg.2 hb1), mul_nonneg hf0 (sub_nonneg.2 hf1),
    mul_nonneg (mul_nonneg hb0 hb0) (sub_nonneg.2 hb1), mul_nonneg (mul_nonneg hf0 hb0) (sub_nonneg.2 hb1)]

lemma twoAlphaGamma (d b : ℝ) (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    0 ≤ -4 * b ^ 4 + 6 * b ^ 3 * d + 2 * b ^ 3 - 4 * b ^ 2 * d ^ 2 - 2 * b ^ 2 * d + 4 * b ^ 2
      + 8 * d ^ 2 - 8 * b * d := by
  nlinarith [mul_nonneg hd0 hb0, mul_nonneg (sub_nonneg.2 hd1) (sub_nonneg.2 hb1),
    mul_nonneg hb0 (sub_nonneg.2 hb1), mul_nonneg hd0 (sub_nonneg.2 hd1), sq_nonneg (b - 2 * d),
    mul_nonneg (mul_nonneg hb0 hb0) (sub_nonneg.2 hb1), sq_nonneg (b - d)]

lemma C_nonpos (f b : ℝ) (hf0 : 0 ≤ f) (hf1 : f ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    -b ^ 4 * (1 + f) ^ 2 + 2 * b ^ 3 * (1 + f) - 8 * b + 4 * b ^ 2 * (1 + f) ≤ 0 := by
  have e : -b ^ 4 * (1 + f) ^ 2 + 2 * b ^ 3 * (1 + f) - 8 * b + 4 * b ^ 2 * (1 + f)
      = -(b * ((2 - (1 + f) * b) * (4 - (1 + f) * b ^ 2))) := by ring
  rw [e]
  have h1 : 0 ≤ 2 - (1 + f) * b := by nlinarith
  have h2 : 0 ≤ 4 - (1 + f) * b ^ 2 := by nlinarith [mul_nonneg hb0 hb0]
  have := mul_nonneg hb0 (mul_nonneg h1 h2)
  linarith

/-! ## Generic one-variable facts -/

lemma quad_up (A B C x y : ℝ) (hC : C ≤ 0) (hAB : 0 ≤ 2 * A + B) (hx : 0 ≤ x) (hxy : x ≤ y)
    (hy : y ≤ 1) (h : 0 < A * x ^ 2 + B * x + C) : 0 < A * y ^ 2 + B * y + C := by
  rcases le_or_gt 0 A with hA | hA
  · have hx' : 0 < x := by
      rcases hx.lt_or_eq with h' | h'
      · exact h'
      · subst h'; nlinarith
    have key : x * (A * y ^ 2 + B * y + C)
        = y * (A * x ^ 2 + B * x + C) + (y - x) * (-C) + A * x * y * (y - x) := by ring
    have h1 : 0 < y * (A * x ^ 2 + B * x + C) := mul_pos (by linarith) h
    have h2 : 0 ≤ (y - x) * (-C) := mul_nonneg (by linarith) (by linarith)
    have h3 : 0 ≤ A * x * y * (y - x) :=
      mul_nonneg (mul_nonneg (mul_nonneg hA hx) (by linarith)) (by linarith)
    have h4 : 0 < x * (A * y ^ 2 + B * y + C) := by rw [key]; linarith
    by_contra hc
    push Not at hc
    nlinarith [mul_nonneg hx'.le (neg_nonneg.2 hc)]
  · have key : A * y ^ 2 + B * y + C - (A * x ^ 2 + B * x + C) = (y - x) * (A * (x + y) + B) := by
      ring
    have h1 : 0 ≤ A * (x + y) + B := by nlinarith [mul_nonneg (neg_nonneg.2 hA.le) (show 0 ≤ 2 - x - y by linarith)]
    have := mul_nonneg (sub_nonneg.2 hxy) h1
    linarith

lemma quad_mono (α γ ε x y : ℝ) (hα : α ≤ 0) (h : 0 ≤ 2 * α + γ) (hx : 0 ≤ x) (hxy : x ≤ y)
    (hy : y ≤ 1) : α * x ^ 2 + γ * x + ε ≤ α * y ^ 2 + γ * y + ε := by
  have key : α * y ^ 2 + γ * y + ε - (α * x ^ 2 + γ * x + ε) = (y - x) * (α * (x + y) + γ) := by ring
  have h1 : 0 ≤ α * (x + y) + γ := by nlinarith [mul_nonneg (neg_nonneg.2 hα) (show 0 ≤ 2 - x - y by linarith)]
  have := mul_nonneg (sub_nonneg.2 hxy) h1
  linarith

lemma upper_thresh (g : ℝ → ℝ) (hg : Continuous g)
    (hmono : ∀ x y : ℝ, 0 ≤ x → x ≤ y → y ≤ 1 → 0 < g x → 0 < g y) :
    ∃ t : ℝ, ∀ x : ℝ, 0 ≤ x → x ≤ 1 → (0 < g x ↔ t < x) := by
  set T : Set ℝ := Set.Icc 0 1 ∩ {x | g x ≤ 0} with hT
  have hTc : IsCompact T :=
    isCompact_Icc.of_isClosed_subset (isClosed_Icc.inter (isClosed_le hg continuous_const))
      Set.inter_subset_left
  rcases T.eq_empty_or_nonempty with h | h
  · refine ⟨-1, fun x hx0 hx1 => ⟨fun _ => by linarith, fun _ => ?_⟩⟩
    by_contra hc
    push Not at hc
    have hm : x ∈ T := ⟨⟨hx0, hx1⟩, hc⟩
    rw [h] at hm
    exact hm
  · refine ⟨sSup T, fun x hx0 hx1 => ⟨fun hx => ?_, fun hx => ?_⟩⟩
    · have hm := hTc.sSup_mem h
      by_contra hc
      push Not at hc
      have h2 := hmono x (sSup T) hx0 hc hm.1.2 hx
      have h3 : g (sSup T) ≤ 0 := hm.2
      linarith
    · by_contra hc
      push Not at hc
      have hm : x ∈ T := ⟨⟨hx0, hx1⟩, hc⟩
      have := le_csSup hTc.bddAbove hm
      linarith

lemma band_thresh (g : ℝ → ℝ) (hg : Continuous g)
    (hq : ∀ x y z : ℝ, 0 ≤ x → x ≤ y → y ≤ z → z ≤ 1 → g x ≤ 0 → g z ≤ 0 → g y ≤ 0) :
    ∃ b1 b2 : ℝ, b1 ≤ b2 ∧ ∀ x : ℝ, 0 ≤ x → x ≤ 1 → (0 < g x ↔ x < b1 ∨ b2 < x) := by
  set T : Set ℝ := Set.Icc 0 1 ∩ {x | g x ≤ 0} with hT
  have hTc : IsCompact T :=
    isCompact_Icc.of_isClosed_subset (isClosed_Icc.inter (isClosed_le hg continuous_const))
      Set.inter_subset_left
  rcases T.eq_empty_or_nonempty with h | h
  · refine ⟨2, 2, le_rfl, fun x hx0 hx1 => ⟨fun _ => Or.inl (by linarith), fun _ => ?_⟩⟩
    by_contra hc
    push Not at hc
    have hm : x ∈ T := ⟨⟨hx0, hx1⟩, hc⟩
    rw [h] at hm
    exact hm
  · have hlo := hTc.sInf_mem h
    have hhi := hTc.sSup_mem h
    refine ⟨sInf T, sSup T, csInf_le_csSup h hTc.bddBelow hTc.bddAbove,
      fun x hx0 hx1 => ⟨fun hx => ?_, fun hx => ?_⟩⟩
    · by_contra hc
      push Not at hc
      have h1 : g (sInf T) ≤ 0 := hlo.2
      have h3 : g (sSup T) ≤ 0 := hhi.2
      have := hq (sInf T) x (sSup T) hlo.1.1 hc.1 hc.2 hhi.1.2 h1 h3
      linarith
    · by_contra hc
      push Not at hc
      have hm : x ∈ T := ⟨⟨hx0, hx1⟩, hc⟩
      rcases hx with hx | hx
      · have := csInf_le hTc.bddBelow hm
        linarith
      · have := le_csSup hTc.bddAbove hm
        linarith

lemma quartic_hasDerivAt (a b c e k m : ℝ) :
    HasDerivAt (fun t : ℝ => a * t ^ 4 + b * t ^ 3 + c * t ^ 2 + e * t + k)
      (4 * a * m ^ 3 + 3 * b * m ^ 2 + 2 * c * m + e) m := by
  have h := ((((hasDerivAt_pow 4 m).const_mul a).add ((hasDerivAt_pow 3 m).const_mul b)).add
    ((hasDerivAt_pow 2 m).const_mul c)).add ((hasDerivAt_id' m).const_mul e) |>.add_const k
  refine h.congr_deriv ?_
  norm_num
  ring

lemma quartic_quasi (a b c e k x y z : ℝ) (g : ℝ → ℝ)
    (hg : ∀ t, g t = a * t ^ 4 + b * t ^ 3 + c * t ^ 2 + e * t + k)
    (hT : ∀ m, x < m → m < z → 4 * a * m ^ 3 + 3 * b * m ^ 2 + 2 * c * m + e = 0 →
      0 < 6 * a * m ^ 2 + 3 * b * m + c)
    (hxy : x ≤ y) (hyz : y ≤ z) (h1 : g x ≤ 0) (h3 : g z ≤ 0) : g y ≤ 0 := by
  by_contra hy
  push Not at hy
  have hgf : g = fun t : ℝ => a * t ^ 4 + b * t ^ 3 + c * t ^ 2 + e * t + k := funext hg
  have hcont : Continuous g := by rw [hgf]; fun_prop
  obtain ⟨m, hm, hmax⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.2 (hxy.trans hyz))
    hcont.continuousOn
  have hym : g y ≤ g m := isMaxOn_iff.mp hmax y ⟨hxy, hyz⟩
  have hxm : x < m := lt_of_le_of_ne hm.1 (by rintro rfl; linarith)
  have hmz : m < z := lt_of_le_of_ne hm.2 (by rintro rfl; linarith)
  have hloc : IsLocalMax g m := hmax.isLocalMax (Icc_mem_nhds hxm hmz)
  have hderiv : HasDerivAt g (4 * a * m ^ 3 + 3 * b * m ^ 2 + 2 * c * m + e) m := by
    rw [hgf]; exact quartic_hasDerivAt a b c e k m
  have h0 := hloc.hasDerivAt_eq_zero hderiv
  have hK0 := hT m hxm hmz h0
  have hKc : Continuous (fun h : ℝ => (6 * a * m ^ 2 + 3 * b * m + c) + (4 * a * m + b) * h + a * h ^ 2) := by
    fun_prop
  have hK0' : 0 < (6 * a * m ^ 2 + 3 * b * m + c) + (4 * a * m + b) * 0 + a * 0 ^ 2 := by
    norm_num; exact hK0
  have hev1 : ∀ᶠ h in nhds (0 : ℝ), 0 < (6 * a * m ^ 2 + 3 * b * m + c) + (4 * a * m + b) * h + a * h ^ 2 :=
    (hKc.tendsto 0).eventually (lt_mem_nhds hK0')
  have hten : Filter.Tendsto (fun h : ℝ => m + h) (nhds 0) (nhds m) := by
    simpa using (continuous_const_add m).tendsto (0 : ℝ)
  have hev2 : ∀ᶠ h in nhds (0 : ℝ), g (m + h) ≤ g m := hten.eventually hloc
  have hev3 : ∀ᶠ h in nhdsWithin (0 : ℝ) {0}ᶜ,
      (0 < (6 * a * m ^ 2 + 3 * b * m + c) + (4 * a * m + b) * h + a * h ^ 2 ∧ g (m + h) ≤ g m) ∧
        h ∈ ({0}ᶜ : Set ℝ) :=
    ((hev1.and hev2).filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
  obtain ⟨h, ⟨hK, hle⟩, hne⟩ := hev3.exists
  have hne' : h ≠ 0 := hne
  have htay : g (m + h) - g m = h ^ 2 * ((6 * a * m ^ 2 + 3 * b * m + c) + (4 * a * m + b) * h + a * h ^ 2)
      + h * (4 * a * m ^ 3 + 3 * b * m ^ 2 + 2 * c * m + e) := by
    rw [hg, hg]; ring
  rw [h0, mul_zero, add_zero] at htay
  have hh2 : 0 < h ^ 2 := by positivity
  have := mul_pos hh2 hK
  linarith

/-! ## The model -/

lemma P11_eq_sub (d f b : ℝ) : P11 d f b = 2 * N5 d f b - D d f b := by
  unfold P11 N5 D; ring

lemma omega_imp (d f b : ℝ) (h : Omega d f b) : 0 < P11 d f b := by
  rw [P11_eq_sub]
  unfold Omega H at h
  by_cases hc : cond5 d f b
  · rw [if_pos hc] at h
    unfold cond5 at hc
    by_cases hD : D d f b = 0
    · rw [hD] at h; norm_num at h
    · have hD2 : 0 < D d f b ^ 2 := by positivity
      rw [lt_div_iff₀ hD2] at h
      by_contra hn
      push Not at hn
      nlinarith [mul_nonneg (sub_nonneg.2 hn) (show 0 ≤ D d f b + 2 * N5 d f b by linarith)]
  · rw [if_neg hc] at h; norm_num at h

lemma omega_of_Dpos (d f b : ℝ) (hD : 0 < D d f b) (h : 0 < P11 d f b) : Omega d f b := by
  rw [P11_eq_sub] at h
  have hN : 0 < N5 d f b := by linarith
  unfold Omega H
  rw [if_pos (show cond5 d f b from hN)]
  rw [lt_div_iff₀ (by positivity)]
  nlinarith [mul_pos h (show 0 < 2 * N5 d f b + D d f b by linarith)]

lemma P11_delta (d f b : ℝ) : P11 d f b =
    (8 * f - 4 * b + 2 * b ^ 2 * (1 - f ^ 2)) * d ^ 2 +
      (8 + 2 * b ^ 3 * f * (1 + f) - 4 * b * (1 + 2 * f) - 2 * b ^ 2 * f) * d +
      (-b ^ 4 * (1 + f) ^ 2 + 2 * b ^ 3 * (1 + f) - 8 * b + 4 * b ^ 2 * (1 + f)) := by
  unfold P11; ring

lemma P11_f (d f b : ℝ) : P11 d f b =
    (-b ^ 4 + 2 * b ^ 3 * d - 2 * b ^ 2 * d ^ 2) * f ^ 2 +
      (-2 * b ^ 4 + 2 * b ^ 3 * (1 + d) + 8 * d ^ 2 - 8 * b * d + b ^ 2 * (4 - 2 * d)) * f +
      (-b ^ 4 + 8 * d + 2 * b ^ 3 - 4 * b * (2 + d + d ^ 2) + b ^ 2 * (4 + 2 * d ^ 2)) := by
  unfold P11; ring

lemma delta_mono (d1 d2 f b : ℝ) (h0 : 0 ≤ d1) (h12 : d1 ≤ d2) (h2 : d2 ≤ 1) (hf0 : 0 ≤ f)
    (hf1 : f ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hp : 0 < P11 d1 f b) : 0 < P11 d2 f b := by
  rw [P11_delta] at hp ⊢
  exact quad_up _ _ _ d1 d2 (C_nonpos f b hf0 hf1 hb0 hb1) (twoAB f b hf0 hf1 hb0 hb1) h0 h12 h2 hp

lemma f_mono (d f1 f2 b : ℝ) (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (h0 : 0 ≤ f1) (h12 : f1 ≤ f2) (h2 : f2 ≤ 1)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) : P11 d f1 b ≤ P11 d f2 b := by
  rw [P11_f, P11_f d f2 b]
  apply quad_mono _ _ _ f1 f2 _ _ h0 h12 h2
  · have e : -b ^ 4 + 2 * b ^ 3 * d - 2 * b ^ 2 * d ^ 2 = -(b ^ 2 * ((b - d) ^ 2 + d ^ 2)) := by ring
    rw [e]
    have := mul_nonneg (sq_nonneg b) (add_nonneg (sq_nonneg (b - d)) (sq_nonneg d))
    linarith
  · have := twoAlphaGamma d b hd0 hd1 hb0 hb1
    linarith

lemma P11_half (f b : ℝ) : P11 (b / 2) f b =
    (-b ^ 4 * (1 + f) ^ 2 + 2 * b ^ 3 * (1 + f) - 8 * b + 4 * b ^ 2 * (1 + f)) / 2 := by
  unfold P11; ring

lemma lt_two_d (d f b : ℝ) (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (hf0 : 0 ≤ f) (hf1 : f ≤ 1) (hb0 : 0 ≤ b)
    (hb1 : b ≤ 1) (hp : 0 < P11 d f b) : b < 2 * d := by
  by_contra hc
  push Not at hc
  have := delta_mono d (b / 2) f b hd0 (by linarith) (by linarith) hf0 hf1 hb0 hb1 hp
  rw [P11_half] at this
  have := C_nonpos f b hf0 hf1 hb0 hb1
  linarith

lemma D_lower (d f b : ℝ) (hd1 : d ≤ 1) (hf0 : 0 ≤ f) (hf1 : f ≤ 1) (hb0 : 0 ≤ b)
    (hb1 : b ≤ 1) (h2 : b ≤ 2 * d) : 4 * (1 - f) ≤ D d f b := by
  have key : (1 - b / 2) * (D d f b - 4 * (1 - f)) =
      (1 - d) * (((1/2) * f ^ 2 * b ^ 4 + f * b ^ 4 - 4 * f * b ^ 2 + (1/2) * b ^ 4 - 4 * b ^ 2 + 8) - 4 * (1 - f)) + (d - b / 2) * ((f ^ 2 * b ^ 4 - 2 * f ^ 2 * b ^ 3 + 2 * f ^ 2 * b ^ 2 + 2 * f * b ^ 4 - 2 * f * b ^ 3 - 6 * f * b ^ 2 + 8 * f * b - 8 * f + b ^ 4 - 10 * b ^ 2 + 8 * b + 8) - 4 * (1 - f))
        + (8 * f + 2 * b ^ 2 * (1 - f ^ 2)) * ((d - b / 2) * (1 - d) * (1 - b / 2)) := by
    unfold D; ring
  have hA := dh_poly f b hf0 (by linarith) hb0 (by linarith)
  have hB := d1_poly f b hf0 (by linarith) hb0 (by linarith)
  have hC : 0 ≤ 8 * f + 2 * b ^ 2 * (1 - f ^ 2) := by
    have : 0 ≤ 1 - f ^ 2 := by nlinarith
    positivity
  have hR : 0 ≤ (1 - d) * (((1/2) * f ^ 2 * b ^ 4 + f * b ^ 4 - 4 * f * b ^ 2 + (1/2) * b ^ 4 - 4 * b ^ 2 + 8) - 4 * (1 - f)) + (d - b / 2) * ((f ^ 2 * b ^ 4 - 2 * f ^ 2 * b ^ 3 + 2 * f ^ 2 * b ^ 2 + 2 * f * b ^ 4 - 2 * f * b ^ 3 - 6 * f * b ^ 2 + 8 * f * b - 8 * f + b ^ 4 - 10 * b ^ 2 + 8 * b + 8) - 4 * (1 - f))
        + (8 * f + 2 * b ^ 2 * (1 - f ^ 2)) * ((d - b / 2) * (1 - d) * (1 - b / 2)) := by
    have i1 := mul_nonneg (show 0 ≤ 1 - d by linarith) (sub_nonneg.2 hA)
    have i2 := mul_nonneg (show 0 ≤ d - b / 2 by linarith) (sub_nonneg.2 hB)
    have i3 := mul_nonneg hC (mul_nonneg (mul_nonneg (show 0 ≤ d - b / 2 by linarith)
      (show 0 ≤ 1 - d by linarith)) (show 0 ≤ 1 - b / 2 by linarith))
    linarith
  rw [← key] at hR
  by_contra hc
  push Not at hc
  nlinarith [mul_pos (show 0 < 1 - b / 2 by linarith) (sub_pos.2 hc)]

lemma omega_iff (d f b : ℝ) (hbox : InBox d f b) : Omega d f b ↔ 0 < P11 d f b := by
  obtain ⟨hd0, hd1, hf0, hf1, hb0, hb1⟩ := hbox
  refine ⟨omega_imp d f b, fun h => omega_of_Dpos d f b ?_ h⟩
  have h2 := lt_two_d d f b hd0 hd1 hf0 hf1.le hb0 hb1 h
  have := D_lower d f b hd1 hf0 hf1.le hb0 hb1 h2.le
  linarith

lemma beta_quasi (d f : ℝ) (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (hf0 : 0 ≤ f) (hf1 : f ≤ 1) :
    ∀ x y z : ℝ, 0 ≤ x → x ≤ y → y ≤ z → z ≤ 1 →
      P11 d f x ≤ 0 → P11 d f z ≤ 0 → P11 d f y ≤ 0 := by
  intro x y z hx hxy hyz hz h1 h3
  refine quartic_quasi (-(1 + f) ^ 2) (2 * (1 + f) * (1 + d * f))
    (-2 * d * f + 4 * (1 + f) - 2 * d ^ 2 * (-1 + f ^ 2)) (-4 * (2 + d + d ^ 2 + 2 * d * f))
    (8 * d * (1 + d * f)) x y z (fun t => P11 d f t) (fun t => by unfold P11; ring) ?_ hxy hyz h1 h3
  intro m hxm hmz h0
  have hG := ft_poly d f m hd0 (by linarith) hf0 (by linarith) (by linarith) (by linarith)
  have h0' : m * (4 * -(1 + f) ^ 2 * m ^ 3 + 3 * (2 * (1 + f) * (1 + d * f)) * m ^ 2 +
      2 * (-2 * d * f + 4 * (1 + f) - 2 * d ^ 2 * (-1 + f ^ 2)) * m +
      -4 * (2 + d + d ^ 2 + 2 * d * f)) = 0 := by rw [h0, mul_zero]
  linarith

end E30B5F0B

open E30B5F0B in
open PlatformEntry.Regimes in
theorem solution :
    (∀ δ f β cS a e : ℝ, InBox δ f β → a + e ≠ 0 →
      (profitN δ f β cS a e < profitE δ f β cS a e ↔ Omega δ f β)) ∧
    (∀ f β : ℝ, 0 ≤ f → f < 1 → 0 ≤ β → β ≤ 1 →
      ∃ δt : ℝ, ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 → (Omega δ f β ↔ δt < δ)) ∧
    (∀ δ β : ℝ, 0 ≤ δ → δ ≤ 1 → 0 ≤ β → β ≤ 1 →
      ∃ ft : ℝ, ∀ f : ℝ, 0 ≤ f → f < 1 → (Omega δ f β ↔ ft < f)) ∧
    (∀ δ f : ℝ, 0 ≤ δ → δ ≤ 1 → 0 ≤ f → f < 1 →
      ∃ β₁ β₂ : ℝ, β₁ ≤ β₂ ∧
        ∀ β : ℝ, 0 ≤ β → β ≤ 1 → (Omega δ f β ↔ β < β₁ ∨ β₂ < β)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro δ f β cS a e hbox hae
    have hf : 0 < 1 - f := by linarith [hbox.2.2.2.1]
    have hsq : 0 < (a + e) ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hae))
    have hX : 0 < (1 - f) * (a + e) ^ 2 := mul_pos hf hsq
    unfold profitN profitE Omega
    constructor
    · intro h
      by_contra hc
      push Not at hc
      nlinarith [mul_nonneg (sub_nonneg.2 hc) hX.le]
    · intro h
      nlinarith [mul_pos (sub_pos.2 h) hX]
  · intro f β hf0 hf1 hb0 hb1
    obtain ⟨t, ht⟩ := upper_thresh (fun d => P11 d f β) (by unfold P11; fun_prop)
      (fun x y hx hxy hy h => delta_mono x y f β hx hxy hy hf0 hf1.le hb0 hb1 h)
    refine ⟨t, fun δ h0 h1 => ?_⟩
    rw [omega_iff δ f β ⟨h0, h1, hf0, hf1, hb0, hb1⟩]
    exact ht δ h0 h1
  · intro δ β hd0 hd1 hb0 hb1
    obtain ⟨t, ht⟩ := upper_thresh (fun f => P11 δ f β) (by unfold P11; fun_prop)
      (fun x y hx hxy hy h => lt_of_lt_of_le h (f_mono δ x y β hd0 hd1 hx hxy hy hb0 hb1))
    refine ⟨t, fun f h0 h1 => ?_⟩
    rw [omega_iff δ f β ⟨hd0, hd1, h0, h1, hb0, hb1⟩]
    exact ht f h0 h1.le
  · intro δ f hd0 hd1 hf0 hf1
    obtain ⟨b1, b2, hle, hb⟩ := band_thresh (fun β => P11 δ f β) (by unfold P11; fun_prop)
      (fun x y z hx hxy hyz hz h1 h3 => beta_quasi δ f hd0 hd1 hf0 hf1.le x y z hx hxy hyz hz h1 h3)
    refine ⟨b1, b2, hle, fun β h0 h1 => ?_⟩
    rw [omega_iff δ f β ⟨hd0, hd1, hf0, hf1, h0, h1⟩]
    exact hb β h0 h1
