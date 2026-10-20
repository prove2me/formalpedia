-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P26.choi_composition
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T00:48:00.973625+00:00
-- url     : https://prove2.me/submissions/ef8f758f-7cd2-44a7-b1e7-d51a04d2a328

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

/-- PDF p.3, Theorem 1. The printed name M for the composite is corrected to C=N∘M. -/
theorem solution {I J O : Type*} [Fintype I] [Fintype J] [Fintype O]
    [Nonempty I] [Nonempty J] [Nonempty O]
    (M : Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ)
    (N : Matrix J J ℂ →ₗ[ℂ] Matrix O O ℂ) :
    outputFirstChoi (N.comp M) = channelLink (outputFirstChoi N) (outputFirstChoi M) := by
  ext ⟨o, i⟩ ⟨o', i'⟩
  simp only [channelLink, g52b_choi_apply, LinearMap.comp_apply]
  rw [g52b_lin_expand N (M (Matrix.single i i' 1))]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  ring


end

