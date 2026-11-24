-- Prove2me | solution 1 for ValueEquivalence.finrank_two_sided_kernel
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T00:31:06.952359+00:00
-- url     : https://prove2.me/submissions/365aff8e-6eb8-4229-b018-66e631a9cb6e

import Mathlib
import Definitions.Def_ValueEquivalence_Basic

set_option autoImplicit false

open Filter Topology

open ValueEquivalence

/-- Over a field, `rank (f ⊗ g) = rank f * rank g`. -/
private lemma finrank_range_tensor_map {K M N P Q : Type*} [Field K]
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    [AddCommGroup P] [Module K P] [AddCommGroup Q] [Module K Q]
    [FiniteDimensional K P] [FiniteDimensional K Q]
    (f : M →ₗ[K] P) (g : N →ₗ[K] Q) :
    Module.finrank K (LinearMap.range (TensorProduct.map f g)) =
      Module.finrank K (LinearMap.range f) * Module.finrank K (LinearMap.range g) := by
  have hfac : TensorProduct.map f g =
      TensorProduct.mapIncl (LinearMap.range f) (LinearMap.range g) ∘ₗ
        TensorProduct.map f.rangeRestrict g.rangeRestrict := by
    rw [← TensorProduct.map_comp]
    rfl
  rw [hfac, LinearMap.range_comp_of_range_eq_top]
  · rw [LinearMap.finrank_range_of_inj]
    · exact Module.finrank_tensorProduct
    · exact TensorProduct.map_injective_of_flat_flat _ _
        (Submodule.injective_subtype _) (Submodule.injective_subtype _)
  · rw [LinearMap.range_eq_top]
    exact TensorProduct.map_surjective f.surjective_rangeRestrict g.surjective_rangeRestrict

/-- `rank (X ⊗ₖ Y) = rank X * rank Y`. -/
private lemma rank_kronecker {a b c d : ℕ} (X : Matrix (Fin a) (Fin b) ℝ)
    (Y : Matrix (Fin c) (Fin d) ℝ) :
    (Matrix.kroneckerMap (· * ·) X Y).rank = X.rank * Y.rank := by
  rw [Matrix.rank_eq_finrank_range_toLin (Matrix.kroneckerMap (· * ·) X Y)
      ((Pi.basisFun ℝ (Fin a)).tensorProduct (Pi.basisFun ℝ (Fin c)))
      ((Pi.basisFun ℝ (Fin b)).tensorProduct (Pi.basisFun ℝ (Fin d))),
    Matrix.toLin_kronecker, finrank_range_tensor_map,
    ← Matrix.rank_eq_finrank_range_toLin, ← Matrix.rank_eq_finrank_range_toLin]

/-- Vectorization as a linear equivalence. -/
private def vecEquiv (n m : ℕ) : Matrix (Fin n) (Fin m) ℝ ≃ₗ[ℝ] (Fin m × Fin n → ℝ) where
  toFun := Matrix.vec
  map_add' := Matrix.vec_add
  map_smul' := fun r B => Matrix.vec_smul r B
  invFun := fun v => Matrix.of fun i j => v (j, i)
  left_inv := fun B => by ext i j; rfl
  right_inv := fun v => by ext ⟨j, i⟩; rfl

theorem solution {k n m l : ℕ} (A : Matrix (Fin k) (Fin n) ℝ)
    (C : Matrix (Fin m) (Fin l) ℝ) :
    (Module.finrank ℝ (twoSidedKernel A C) : ℤ) = (n : ℤ) * m - (A.rank : ℤ) * C.rank := by
  set K := Matrix.kroneckerMap (· * ·) (Matrix.transpose C) A with hK
  have hker : twoSidedKernel A C =
      (LinearMap.ker K.mulVecLin).comap (vecEquiv n m).toLinearMap := by
    ext B
    change A * B * C = 0 ↔ K.mulVec (Matrix.vec B) = 0
    rw [hK, Matrix.kronecker_mulVec_vec, Matrix.transpose_transpose, Matrix.vec_eq_zero_iff]
  have hdim : Module.finrank ℝ (twoSidedKernel A C) =
      Module.finrank ℝ (LinearMap.ker K.mulVecLin) := by
    rw [hker, Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq]
  have hrn := LinearMap.finrank_range_add_finrank_ker K.mulVecLin
  have hrank : Module.finrank ℝ (LinearMap.range K.mulVecLin) = C.rank * A.rank := by
    change K.rank = _
    rw [hK, rank_kronecker, Matrix.rank_transpose]
  rw [hrank, Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_fin] at hrn
  rw [hdim]
  have : (C.rank * A.rank : ℕ) + Module.finrank ℝ (LinearMap.ker K.mulVecLin) = m * n := hrn
  zify at this
  linarith
