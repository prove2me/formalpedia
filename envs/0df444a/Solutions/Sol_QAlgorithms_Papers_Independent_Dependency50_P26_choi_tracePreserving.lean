-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P26.choi_tracePreserving
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T00:51:28.111335+00:00
-- url     : https://prove2.me/submissions/7a79c9fb-7dcd-4be5-a267-edfc4b9c43db

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P26

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms

attribute [local instance] Classical.decEq Classical.propDecidable

open QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Dependency50 QAlgorithms.Papers.Independent.Dependency50.P26

theorem g52b_choi_apply {I O : Type*} [Fintype I] (M : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    (o o' : O) (i i' : I) :
    outputFirstChoi M (o, i) (o', i') = M (Matrix.single i i' 1) o o' := rfl

theorem g52b_lin_expand {I O : Type*} [Fintype I] (M : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    (X : Matrix I I ℂ) : M X = ∑ i, ∑ j, X i j • M (Matrix.single i j 1) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single X]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]

/-- PDF p.2, Lemma 1. Finite nonempty coordinate types carry the fixed bases. -/
theorem solution {I O : Type*} [Fintype I] [Fintype O]
    [Nonempty I] [Nonempty O] (M : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) :
    TracePreserving M ↔ traceLeft (outputFirstChoi M) = 1 := by
  constructor
  · intro h
    ext i i'
    simp only [traceLeft, Matrix.of_apply, g52b_choi_apply, Matrix.one_apply]
    have := h (Matrix.single i i' 1)
    simp only [Matrix.trace, Matrix.diag] at this
    rw [this]
    by_cases hii : i = i'
    · subst hii; simp [Matrix.diag, Matrix.single_apply]
    · simp [Matrix.diag, Matrix.single_apply, hii, Ne.symm hii]
  · intro h X
    have hd : ∀ i i', (M (Matrix.single i i' 1)).trace = if i = i' then 1 else 0 := by
      intro i i'
      have := congrFun (congrFun h i) i'
      simp only [traceLeft, Matrix.of_apply, g52b_choi_apply, Matrix.one_apply] at this
      simpa [Matrix.trace] using this
    rw [g52b_lin_expand M X]
    simp only [Matrix.trace_sum, Matrix.trace_smul, hd, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rfl


end

