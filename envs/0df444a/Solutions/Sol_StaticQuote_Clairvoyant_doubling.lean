-- Prove2me | solution 1 for StaticQuote.Clairvoyant.doubling
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T14:59:45.038842+00:00
-- url     : https://prove2.me/submissions/577a44bf-87e2-4feb-8362-c5548733b6d9

import Mathlib
import Definitions.Def_StaticQuote_Clairvoyant_Setting
import Theorems.Thm_StaticQuote_Clairvoyant_superadditive
import Theorems.Thm_StaticQuote_Clairvoyant_block_stationary

open MeasureTheory Filter
open scoped ENNReal
open StaticQuote.Clairvoyant

theorem solution {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (Q : Model Ω)
    (hQ : Q.Standing μ) (N : ℕ) :
    2 * ∫⁻ ω, Q.gamma 1 N ω ∂μ ≤ ∫⁻ ω, Q.gamma 1 (2 * N) ω ∂μ := by
  calc 2 * ∫⁻ ω, Q.gamma 1 N ω ∂μ
      = ∫⁻ ω, Q.gamma 1 N ω ∂μ + ∫⁻ ω, Q.gamma (N + 1) (2 * N) ω ∂μ := by
        rw [two_mul, ← block_stationary Q hQ N]
    _ ≤ ∫⁻ ω, (Q.gamma 1 N ω + Q.gamma (N + 1) (2 * N) ω) ∂μ := le_lintegral_add _ _
    _ ≤ ∫⁻ ω, Q.gamma 1 (2 * N) ω ∂μ := lintegral_mono fun ω => superadditive Q ω N
