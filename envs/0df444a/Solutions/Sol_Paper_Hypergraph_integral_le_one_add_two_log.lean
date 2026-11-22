-- Prove2me | solution 1 for Paper.Hypergraph.integral_le_one_add_two_log
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:16:57.161589+00:00
-- url     : https://prove2.me/submissions/c9788021-e125-43ec-a684-9cfdd1fed306

import Definitions.Def_Paper_TwoTerminalRounding
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Definitions.Def_Paper_RoundingAveraging

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open MeasureTheory Set
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution {f : ℝ → ℝ} {M : ℝ}
    (hf : Measurable f) (hn : ∀ r, 0 ≤ f r) (hM : 1 ≤ M)
    (hb : ∀ r, f r ≤ M)
    (htail : ∀ t, 1 ≤ t → levelMeasure.real {r | t ≤ f r} ≤ 2 / t) :
    ∫ r, f r ∂levelMeasure ≤ 1 + 2 * Real.log M := by
  have hi : Integrable f levelMeasure :=
    (integrable_const M).mono' hf.aestronglyMeasurable
      (Filter.Eventually.of_forall fun r => by simpa [Real.norm_eq_abs, abs_of_nonneg (hn r)] using hb r)
  let g : ℝ → ℝ := fun t => levelMeasure.real {r | t ≤ f r}
  have hganti : Antitone g := by
    intro a b hab
    exact measureReal_mono (fun r hr => hab.trans hr)
  have hgn : ∀ t, 0 ≤ g t := fun _ => ENNReal.toReal_nonneg
  have hgb : ∀ t, g t ≤ 1 := fun _ => measureReal_le_one
  have hgi (a b : ℝ) : IntervalIntegrable g volume a b := by
    have h : IntegrableOn g (uIcc a b) volume :=
      (integrableOn_const (C := (1 : ℝ)) isCompact_uIcc.measure_ne_top).mono' hganti.measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => by simpa [Real.norm_eq_abs, abs_of_nonneg (hgn t)] using hgb t)
    exact h.intervalIntegrable
  rw [hi.integral_eq_integral_Ioc_meas_le
    (Filter.Eventually.of_forall hn) (Filter.Eventually.of_forall hb)]
  change (∫ t in Ioc 0 M, g t) ≤ _
  rw [← intervalIntegral.integral_of_le (by linarith : (0 : ℝ) ≤ M),
    ← intervalIntegral.integral_add_adjacent_intervals (hgi 0 1) (hgi 1 M)]
  have hfirst : (∫ t in (0 : ℝ)..1, g t) ≤ 1 := by
    calc
      _ ≤ ∫ _ in (0 : ℝ)..1, (1 : ℝ) :=
        intervalIntegral.integral_mono_on (by norm_num) (hgi 0 1) intervalIntegrable_const
          (fun t ht => hgb t)
      _ = 1 := by simp
  have hinv : IntervalIntegrable (fun t : ℝ => 2 / t) volume 1 M := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_const.div continuousOn_id
    intro t ht
    rw [uIcc_of_le hM] at ht
    change t ≠ 0
    linarith [ht.1]
  have hlast : (∫ t in (1 : ℝ)..M, g t) ≤ 2 * Real.log M := by
    calc
      _ ≤ ∫ t in (1 : ℝ)..M, 2 / t :=
        intervalIntegral.integral_mono_on hM (hgi 1 M) hinv (fun t ht => htail t ht.1)
      _ = 2 * Real.log M := by
        simp only [div_eq_mul_inv, intervalIntegral.integral_const_mul,
          integral_inv_of_pos (by norm_num : (0 : ℝ) < 1) (by linarith : 0 < M), inv_one, mul_one]
  exact add_le_add hfirst hlast
end Paper.Hypergraph
