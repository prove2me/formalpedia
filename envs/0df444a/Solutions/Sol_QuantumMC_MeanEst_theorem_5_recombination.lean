-- Prove2me | solution 1 for QuantumMC.MeanEst.theorem_5_recombination
-- status  : ACCEPTED   (prove)
-- author  : @mihalyimark
-- created : 2026-10-18T17:55:08.345967+00:00
-- url     : https://prove2.me/submissions/0196743a-7b09-493a-85b6-c83d8a04a68b

import Mathlib
import Definitions.Def_QuantumMC_MeanEst_Setting

open MeasureTheory ProbabilityTheory Filter
open QuantumMC.MeanEst

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Integrable X P)
    (σ m : ℝ) (hσ : 0 < σ) :
    (∫ ω, X ω ∂P) = σ *
      (m - (∫ ω, -(truncLt 0 (alg3B σ m X) ω) ∂P) +
        (∫ ω, truncGe 0 (alg3B σ m X) ω ∂P)) := by
  let B : Ω → ℝ := alg3B σ m X
  change (∫ ω, X ω ∂P) =
    σ * (m - (∫ ω, -(truncLt 0 B ω) ∂P) + (∫ ω, truncGe 0 B ω ∂P))
  have hσne : σ ≠ 0 := ne_of_gt hσ
  have hBint : Integrable B P := by
    have : B = fun ω => X ω / σ - m := rfl
    rw [this]
    exact (hX.div_const σ).sub (integrable_const m)
  -- Pointwise: `toNNReal (B ω)` is the positive part, matching `truncGe 0 B`.
  have hCpt : ∀ ω, (Real.toNNReal (B ω) : ℝ) = truncGe 0 B ω := by
    intro ω
    rw [Real.coe_toNNReal']
    by_cases h : 0 ≤ B ω
    · rw [max_eq_left h, truncGe, if_pos h]
    · rw [max_eq_right (le_of_lt (lt_of_not_ge h)), truncGe, if_neg h]
  -- Pointwise: `toNNReal (-(B ω))` is the negative part, matching `-(truncLt 0 B)`.
  have hApt : ∀ ω, (Real.toNNReal (-(B ω)) : ℝ) = -(truncLt 0 B ω) := by
    intro ω
    rw [Real.coe_toNNReal']
    by_cases h : 0 ≤ B ω
    · rw [max_eq_right (neg_nonpos.mpr h), truncLt, if_neg (not_lt.mpr h), neg_zero]
    · have hlt : B ω < 0 := lt_of_not_ge h
      rw [max_eq_left (neg_nonneg.mpr (le_of_lt hlt)), truncLt, if_pos hlt]
  have hCint : (∫ ω, (Real.toNNReal (B ω) : ℝ) ∂P) = ∫ ω, truncGe 0 B ω ∂P :=
    integral_congr_ae (Eventually.of_forall hCpt)
  have hAint : (∫ ω, (Real.toNNReal (-(B ω)) : ℝ) ∂P) =
      ∫ ω, -(truncLt 0 B ω) ∂P :=
    integral_congr_ae (Eventually.of_forall hApt)
  -- Split `∫ B` into positive and negative parts.
  have hBdecomp : (∫ ω, B ω ∂P) =
      (∫ ω, truncGe 0 B ω ∂P) - (∫ ω, -(truncLt 0 B ω) ∂P) := by
    rw [integral_eq_integral_pos_part_sub_integral_neg_part hBint, hCint, hAint]
  -- Evaluate `∫ B = (∫ X)/σ - m`.
  have hBval : (∫ ω, B ω ∂P) = (∫ ω, X ω ∂P) / σ - m := by
    have : B = fun ω => X ω / σ - m := rfl
    rw [this, integral_sub (hX.div_const σ) (integrable_const m), integral_div,
      integral_const]
    simp [Measure.real, measure_univ]
  have hXval : (∫ ω, X ω ∂P) = σ * ((∫ ω, B ω ∂P) + m) := by
    rw [hBval, show (∫ ω, X ω ∂P) / σ - m + m = (∫ ω, X ω ∂P) / σ by ring]
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ hσne]
  rw [hXval, hBdecomp]
  ring
