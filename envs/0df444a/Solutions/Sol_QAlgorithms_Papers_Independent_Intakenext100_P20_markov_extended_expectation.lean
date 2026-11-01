-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakenext100.P20.markov_extended_expectation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T00:46:49.539599+00:00
-- url     : https://prove2.me/submissions/52943b40-aa28-4b73-a0b9-38ad761303bd

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P20

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open QAlgorithms.Papers.Independent.Intakenext100.P20

theorem solution {Omega : Type*} [MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (X : Omega → ℝ) (hX : Measurable X) (hpos : ∀ w, 0 < X w)
    (c : ℝ) (hc : 0 < c) :
    mu {w | c ≤ X w} ≤
      MeasureTheory.lintegral mu (fun w => ENNReal.ofReal (X w)) / ENNReal.ofReal c := by
  have hmeas : Measurable (fun w : Omega => ENNReal.ofReal (X w)) :=
    ENNReal.measurable_ofReal.comp hX
  have hset :
      {w : Omega | ENNReal.ofReal c ≤ ENNReal.ofReal (X w)} =
        {w : Omega | c ≤ X w} := by
    ext w
    exact ENNReal.ofReal_le_ofReal_iff (le_of_lt (hpos w))
  have hb := MeasureTheory.mul_meas_ge_le_lintegral (μ := mu) hmeas (ENNReal.ofReal c)
  rw [hset] at hb
  have hc0 : ENNReal.ofReal c ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hc
  have hctop : ENNReal.ofReal c ≠ ⊤ := ENNReal.ofReal_ne_top
  apply (ENNReal.le_div_iff_mul_le (Or.inl hc0) (Or.inl hctop)).2
  simpa [mul_comm] using hb
