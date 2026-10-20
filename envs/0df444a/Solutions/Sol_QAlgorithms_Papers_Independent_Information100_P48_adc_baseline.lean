-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P48.adc_baseline
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T00:46:20.01483+00:00
-- url     : https://prove2.me/submissions/7482c9be-f2df-4400-a947-43854af1e104

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P48

namespace QAlgorithms.Papers.Independent.Information100.P48

open scoped Matrix ComplexConjugate

noncomputable section

theorem g52c_adc_apply (g : ℝ) (hg0 : 0 ≤ g) (X : QOp) (a b : Bool) :
    adc g X a b = ((if a then (Real.sqrt (1 - g) : ℂ) else 1) * (if b then (Real.sqrt (1 - g) : ℂ) else 1)) * X a b
      + (if a = false ∧ b = false then (g : ℂ) * X true true else 0) := by
  have hs : ((Real.sqrt g : ℂ)) * (Real.sqrt g : ℂ) = g := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hg0]
  cases a <;> cases b <;>
    simp [adc, k0, k1, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.conjTranspose_apply]
  all_goals (try rw [← hs]); ring

theorem g52c_temporal_adc (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) :
    temporal (adc g) = 2 * Real.sqrt (2 * (1 - g)) := by
  simp only [temporal, correlator, conditionalJoint, rawJoint, success, projector, mixedQubit]
  simp [g52c_adc_apply g hg0, pauliX, pauliY, outcomeSign, Matrix.mul_apply, Matrix.trace, Fintype.sum_bool]
  have hs2 : Real.sqrt (1 - g) * Real.sqrt (1 - g) = 1 - g := Real.mul_self_sqrt (by linarith)
  rw [hs2]
  have hD : (1 - g) * 2⁻¹ + (2⁻¹ + g * 2⁻¹) = (1:ℝ) := by ring
  rw [hD]
  simp only [div_one]
  ring

end

end QAlgorithms.Papers.Independent.Information100.P48

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Information100 QAlgorithms.Papers.Independent.Information100.P48 in
open scoped Matrix ComplexConjugate in
theorem solution (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) :
    temporal (adc g) = 2 * Real.sqrt (2 * (1 - g)) ∧
    (2 < temporal (adc g) ↔ g < 1 / 2) ∧
    AntitoneOn (fun t => temporal (adc t)) (Set.Icc (0 : ℝ) 1) := by
  refine ⟨g52c_temporal_adc g hg0 hg1, ?_, ?_⟩
  · rw [g52c_temporal_adc g hg0 hg1]
    constructor
    · intro h
      have h1 : 1 < Real.sqrt (2 * (1 - g)) := by linarith
      have h2 : (1:ℝ) ^ 2 < 2 * (1 - g) := (Real.lt_sqrt (by norm_num)).mp h1
      linarith
    · intro h
      have h2 : (1:ℝ) ^ 2 < 2 * (1 - g) := by linarith
      have h1 : 1 < Real.sqrt (2 * (1 - g)) := (Real.lt_sqrt (by norm_num)).mpr h2
      linarith
  · intro s hs t ht hst
    simp only
    rw [g52c_temporal_adc s hs.1 hs.2, g52c_temporal_adc t ht.1 ht.2]
    have : Real.sqrt (2 * (1 - t)) ≤ Real.sqrt (2 * (1 - s)) := Real.sqrt_le_sqrt (by linarith)
    linarith
