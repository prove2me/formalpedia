-- Prove2me | solution 1 for StaticQuote.Clairvoyant.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T14:59:47.702393+00:00
-- url     : https://prove2.me/submissions/566ec744-d3b2-49b6-a4c4-b9db542e601e

import Mathlib
import Definitions.Def_StaticQuote_Clairvoyant_Setting
import Theorems.Thm_StaticQuote_Clairvoyant_eq_14
import Theorems.Thm_StaticQuote_Clairvoyant_eq_15

open MeasureTheory Filter
open scoped ENNReal
open StaticQuote.Clairvoyant

theorem solution {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (Q : Model Ω)
    (hQ : Q.Standing μ) (y : ℕ → Ω → ℝ) (hy : Q.IsFCFSSchedule y) (N : ℕ) (hN : 1 ≤ N) :
    ENNReal.ofReal (Q.rate μ) * ∫⁻ ω, Q.gamma 1 N ω / (N : ℝ≥0∞) ∂μ ≤ Q.cost μ y := by
  calc ENNReal.ofReal (Q.rate μ) * ∫⁻ ω, Q.gamma 1 N ω / (N : ℝ≥0∞) ∂μ
      ≤ ENNReal.ofReal (Q.rate μ) *
          limsup (fun M : ℕ => ∫⁻ ω, Q.gamma 1 M ω / (M : ℝ≥0∞) ∂μ) atTop :=
        by gcongr; exact eq_15 Q hQ N hN
    _ = limsup (fun M : ℕ => ENNReal.ofReal (Q.rate μ) * ∫⁻ ω, Q.gamma 1 M ω / (M : ℝ≥0∞) ∂μ)
          atTop := (ENNReal.limsup_const_mul_of_ne_top ENNReal.ofReal_ne_top).symm
    _ ≤ Q.cost μ y := eq_14 Q hQ y hy
