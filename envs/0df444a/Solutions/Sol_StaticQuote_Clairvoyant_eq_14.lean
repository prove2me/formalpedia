-- Prove2me | solution 1 for StaticQuote.Clairvoyant.eq_14
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T14:59:44.102292+00:00
-- url     : https://prove2.me/submissions/3136ae4a-c705-492b-8165-2d4868c16546

import Mathlib
import Definitions.Def_StaticQuote_Clairvoyant_Setting
import Theorems.Thm_StaticQuote_Clairvoyant_sample_path_bound

open MeasureTheory Filter
open scoped ENNReal
open StaticQuote.Clairvoyant

theorem solution {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (Q : Model Ω) (hQ : Q.Standing μ)
    (y : ℕ → Ω → ℝ) (hy : Q.IsFCFSSchedule y) :
    limsup (fun M : ℕ => ENNReal.ofReal (Q.rate μ) * ∫⁻ ω, Q.gamma 1 M ω / (M : ℝ≥0∞) ∂μ) atTop
      ≤ Q.cost μ y := by
  unfold Model.cost
  rw [← ENNReal.limsup_const_mul_of_ne_top ENNReal.ofReal_ne_top]
  refine limsup_le_limsup (Eventually.of_forall fun M => ?_)
  exact mul_le_mul_of_nonneg_left (lintegral_mono fun ω => sample_path_bound Q y hy ω M) (by positivity)
