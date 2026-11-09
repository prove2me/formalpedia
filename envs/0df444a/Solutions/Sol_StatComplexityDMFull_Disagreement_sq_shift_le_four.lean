-- Prove2me | solution 1 for StatComplexityDMFull.Disagreement.sq_shift_le_four
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T06:15:50.458043+00:00
-- url     : https://prove2.me/submissions/1c2c2226-985e-4257-b836-19c5b4462ba2

import Mathlib
import Definitions.Def_StatComplexityDMFull_Disagreement_RadonLaw
import Definitions.Def_StatComplexityDMFull_Disagreement_MeanModel

set_option autoImplicit false

open MeasureTheory

open StatComplexityDMFull.Disagreement in
theorem solution {M A : Type*} [TopologicalSpace M] [DiscreteTopology M]
    [MeasurableSpace M] [BorelSpace M] [MeasurableSpace A]
    (μ : RadonLaw M) (D : MeanModel M A) (g : A → ℝ) (a : A) :
    (∫ m, (∫ n, (D.mean m a - D.mean n a) ^ 2 ∂μ.val) ∂μ.val) ≤
      2 * (∫ m, (D.mean m a - g a) ^ 2 ∂μ.val) +
      2 * (∫ n, (g a - D.mean n a) ^ 2 ∂μ.val) ∧
    2 * (∫ m, (D.mean m a - g a) ^ 2 ∂μ.val) +
      2 * (∫ n, (g a - D.mean n a) ^ 2 ∂μ.val) =
      4 * (∫ m, (D.mean m a - g a) ^ 2 ∂μ.val) := by
  have hint : ∀ φ : M → ℝ, ∀ C, (∀ m, |φ m| ≤ C) → Integrable φ μ.val := by
    intro φ C h
    exact Integrable.of_bound continuous_of_discreteTopology.measurable.aestronglyMeasurable C
      (ae_of_all _ fun m => by rw [Real.norm_eq_abs]; exact h m)
  have hsq : ∀ z B : ℝ, |z| ≤ B → |z ^ 2| ≤ B ^ 2 := by
    intro z B h
    rw [abs_of_nonneg (sq_nonneg z)]
    exact sq_le_sq' (abs_le.mp h).1 (abs_le.mp h).2
  have hb := fun m => D.range m a
  have hK : Integrable (fun n => (g a - D.mean n a) ^ 2) μ.val := by
    refine hint _ ((1 + |g a|) ^ 2) fun n => hsq _ _ ?_
    rw [abs_le]
    constructor <;> linarith [le_abs_self (g a), neg_abs_le (g a), (hb n).1, (hb n).2]
  have hX : Integrable (fun m => (D.mean m a - g a) ^ 2) μ.val := by
    refine hint _ ((1 + |g a|) ^ 2) fun n => hsq _ _ ?_
    rw [abs_le]
    constructor <;> linarith [le_abs_self (g a), neg_abs_le (g a), (hb n).1, (hb n).2]
  have hi1 : ∀ m, Integrable (fun n => (D.mean m a - D.mean n a) ^ 2) μ.val := by
    intro m
    refine hint _ (1 ^ 2) fun n => hsq _ _ ?_
    rw [abs_le]
    constructor <;> linarith [(hb n).1, (hb n).2, (hb m).1, (hb m).2]
  have hinner : ∀ m, ∫ n, (D.mean m a - D.mean n a) ^ 2 ∂μ.val ≤
      2 * (D.mean m a - g a) ^ 2 + 2 * ∫ n, (g a - D.mean n a) ^ 2 ∂μ.val := by
    intro m
    have i2 : Integrable (fun n => 2 * (D.mean m a - g a) ^ 2 + 2 * (g a - D.mean n a) ^ 2)
        μ.val := (integrable_const _).add (hK.const_mul 2)
    calc ∫ n, (D.mean m a - D.mean n a) ^ 2 ∂μ.val
        ≤ ∫ n, (2 * (D.mean m a - g a) ^ 2 + 2 * (g a - D.mean n a) ^ 2) ∂μ.val :=
          integral_mono (hi1 m) i2 (fun n => by
            have := sq_nonneg (D.mean m a - 2 * g a + D.mean n a)
            nlinarith)
      _ = 2 * (D.mean m a - g a) ^ 2 + 2 * ∫ n, (g a - D.mean n a) ^ 2 ∂μ.val := by
          rw [integral_add (integrable_const _) (hK.const_mul 2), integral_const,
            integral_const_mul]
          simp
  have hO1 : Integrable (fun m => ∫ n, (D.mean m a - D.mean n a) ^ 2 ∂μ.val) μ.val := by
    refine hint _ 1 fun m => ?_
    rw [← Real.norm_eq_abs]
    have := norm_integral_le_of_norm_le_const (μ := μ.val)
      (f := fun n => (D.mean m a - D.mean n a) ^ 2) (C := 1) (ae_of_all _ fun n => by
        rw [Real.norm_eq_abs]
        have := hsq (D.mean m a - D.mean n a) 1 (by
          rw [abs_le]
          constructor <;> linarith [(hb n).1, (hb n).2, (hb m).1, (hb m).2])
        simpa using this)
    simpa using this
  have hO2 : Integrable (fun m => 2 * (D.mean m a - g a) ^ 2 +
      2 * ∫ n, (g a - D.mean n a) ^ 2 ∂μ.val) μ.val := (hX.const_mul 2).add (integrable_const _)
  have hsym : (fun n => (g a - D.mean n a) ^ 2) = fun n => (D.mean n a - g a) ^ 2 := by
    funext n; ring
  refine ⟨?_, ?_⟩
  · calc ∫ m, (∫ n, (D.mean m a - D.mean n a) ^ 2 ∂μ.val) ∂μ.val
        ≤ ∫ m, (2 * (D.mean m a - g a) ^ 2 + 2 * ∫ n, (g a - D.mean n a) ^ 2 ∂μ.val) ∂μ.val :=
          integral_mono hO1 hO2 hinner
      _ = 2 * (∫ m, (D.mean m a - g a) ^ 2 ∂μ.val) +
          2 * (∫ n, (g a - D.mean n a) ^ 2 ∂μ.val) := by
          rw [integral_add (hX.const_mul 2) (integrable_const _), integral_const_mul,
            integral_const]
          simp
  · rw [hsym]; ring
