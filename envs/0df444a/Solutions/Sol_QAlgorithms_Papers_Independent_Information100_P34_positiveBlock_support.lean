-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P34.positiveBlock_support
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T06:35:07.459992+00:00
-- url     : https://prove2.me/submissions/8ba2e747-8d17-41d1-840c-ac8983bd0797

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P34
noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

section X8
variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [FiniteDimensional ℂ G]

private lemma x8_range_adj_comp (a : E →ₗ[ℂ] G) :
    LinearMap.range (a.adjoint ∘ₗ a) = LinearMap.range a.adjoint := by
  have h : (LinearMap.range (a.adjoint ∘ₗ a))ᗮ = (LinearMap.range a.adjoint)ᗮ := by
    rw [LinearMap.orthogonal_range, LinearMap.orthogonal_range, LinearMap.adjoint_comp,
      LinearMap.adjoint_adjoint, LinearMap.ker_adjoint_comp_self]
  rw [← Submodule.orthogonal_orthogonal (LinearMap.range (a.adjoint ∘ₗ a)), h,
    Submodule.orthogonal_orthogonal]

private lemma x8_block (a : E →ₗ[ℂ] G) (y : F →ₗ[ℂ] G) :
    a.adjoint ∘ₗ y =
      (LinearMap.range (a.adjoint ∘ₗ a)).starProjection.toLinearMap ∘ₗ (a.adjoint ∘ₗ y) ∘ₗ
        (LinearMap.range (y.adjoint ∘ₗ y)).starProjection.toLinearMap := by
  ext v
  simp only [LinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coe_coe]
  have hy : y ((LinearMap.range (y.adjoint ∘ₗ y)).starProjection v) = y v := by
    have hmem := Submodule.sub_starProjection_mem_orthogonal
      (K := LinearMap.range (y.adjoint ∘ₗ y)) v
    have hle : LinearMap.range y.adjoint ≤ LinearMap.range (y.adjoint ∘ₗ y) :=
      (x8_range_adj_comp y).ge
    have hmem2 := Submodule.orthogonal_le hle hmem
    rw [LinearMap.orthogonal_range, LinearMap.adjoint_adjoint,
      LinearMap.mem_ker, map_sub, sub_eq_zero] at hmem2
    exact hmem2.symm
  rw [hy]
  symm
  rw [Submodule.starProjection_eq_self_iff, x8_range_adj_comp]
  exact LinearMap.mem_range_self _ _

end X8

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P34 in
theorem solution {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin m) (Fin m) ℂ)
    (C : Matrix (Fin n) (Fin m) ℂ)
    (h : (Matrix.fromBlocks A C Cᴴ B).PosSemidef) :
    C = supportProjector A * C * supportProjector B := by
  classical
  -- factor the block matrix as `Nᴴ N`
  obtain ⟨N, hN⟩ : ∃ N : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℂ,
      Matrix.fromBlocks A C Cᴴ B = Nᴴ * N := by
    open scoped MatrixOrder in
    obtain ⟨X, hX, -, hXe⟩ :=
      CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts h.isHermitian
        (QuasispectrumRestricts.nnreal_of_nonneg h.nonneg)
    refine ⟨X, ?_⟩
    have hs : Xᴴ = X := hX.star_eq
    rw [hs]
    simpa using hXe.symm
  set Xl : Matrix (Fin n ⊕ Fin m) (Fin n) ℂ := N.submatrix id Sum.inl with hXl
  set Yr : Matrix (Fin n ⊕ Fin m) (Fin m) ℂ := N.submatrix id Sum.inr with hYr
  have hA : A = Xlᴴ * Xl := by
    ext i j
    have := congrFun (congrFun hN (Sum.inl i)) (Sum.inl j)
    simpa [Matrix.mul_apply, hXl] using this
  have hC : C = Xlᴴ * Yr := by
    ext i j
    have := congrFun (congrFun hN (Sum.inl i)) (Sum.inr j)
    simpa [Matrix.mul_apply, hXl, hYr] using this
  have hB : B = Yrᴴ * Yr := by
    ext i j
    have := congrFun (congrFun hN (Sum.inr i)) (Sum.inr j)
    simpa [Matrix.mul_apply, hYr] using this
  apply Matrix.toEuclideanLin.injective
  have hT : ∀ (P : Matrix (Fin n) (Fin n) ℂ) (Q : Matrix (Fin m) (Fin m) ℂ),
      Matrix.toEuclideanLin (P * C * Q) =
        Matrix.toEuclideanLin P ∘ₗ Matrix.toEuclideanLin C ∘ₗ Matrix.toEuclideanLin Q := by
    intro P Q
    rw [Matrix.toLpLin_mul (q := 2), Matrix.toLpLin_mul (q := 2)]
    rfl
  rw [hT]
  have hPA : Matrix.toEuclideanLin (supportProjector A) =
      (LinearMap.range (Matrix.toEuclideanLin A)).starProjection.toLinearMap := by
    simp [supportProjector]
  have hPB : Matrix.toEuclideanLin (supportProjector B) =
      (LinearMap.range (Matrix.toEuclideanLin B)).starProjection.toLinearMap := by
    simp [supportProjector]
  have hmul : ∀ {p q r : Type} [Fintype p] [DecidableEq p] [Fintype q] [DecidableEq q]
      [Fintype r] [DecidableEq r] (U : Matrix p q ℂ) (V : Matrix q r ℂ),
      Matrix.toEuclideanLin (U * V) = Matrix.toEuclideanLin U ∘ₗ Matrix.toEuclideanLin V := by
    intro p q r _ _ _ _ _ _ U V
    exact Matrix.toLpLin_mul (p := 2) (q := 2) (r := 2) U V
  rw [hPA, hPB, hA, hB, hC, hmul, hmul, hmul,
    Matrix.toEuclideanLin_conjTranspose_eq_adjoint, Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  exact x8_block _ _
