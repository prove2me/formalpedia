-- Prove2me | solution 1 for Rat.ringOfIntegers_pos_iff_all_real_embeddings
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T22:50:14.577991+00:00
-- url     : https://prove2.me/submissions/70e69f5d-6210-42fe-98b8-0f0c2b5a0a89

import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Data.Real.Basic

theorem solution (a : NumberField.RingOfIntegers ℚ) :
    0 < Rat.ringOfIntegersEquiv a ↔
      ∀ τ : ℚ →+* ℝ, 0 < τ (algebraMap (NumberField.RingOfIntegers ℚ) ℚ a) := by
  have heq (τ : ℚ →+* ℝ) :
      τ (algebraMap (NumberField.RingOfIntegers ℚ) ℚ a) =
        ((Rat.ringOfIntegersEquiv a : ℤ) : ℝ) := by
    calc
      τ (algebraMap (NumberField.RingOfIntegers ℚ) ℚ a) =
          ((algebraMap (NumberField.RingOfIntegers ℚ) ℚ a : ℚ) : ℝ) := eq_ratCast τ _
      _ = ((Rat.ringOfIntegersEquiv a : ℤ) : ℝ) := by
        rw [← Rat.ringOfIntegersEquiv_apply_coe]
        exact Rat.cast_intCast _
  constructor
  · intro h τ
    rw [heq τ]
    exact_mod_cast h
  · intro h
    have hh := h (algebraMap ℚ ℝ)
    rw [heq] at hh
    exact_mod_cast hh
