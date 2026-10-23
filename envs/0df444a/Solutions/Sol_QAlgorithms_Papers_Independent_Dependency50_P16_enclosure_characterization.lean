-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P16.enclosure_characterization
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T00:59:16.989343+00:00
-- url     : https://prove2.me/submissions/baa5fe79-f27b-4d32-b9dd-d6c9823e558e

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P16

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ENNReal NNReal Matrix.Norms.L2Operator

open MeasureTheory Filter

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance 100] LieRing.ofAssociativeRing

namespace QAlgorithms.Papers.Independent.Dependency50.P16

lemma X7EC_act_mul {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (v : EuclideanSpace ℂ (Fin n)) :
    QAlgorithms.act A (QAlgorithms.act B v) = QAlgorithms.act (A * B) v := by
  simp [QAlgorithms.act, Matrix.mulVec_mulVec]

lemma X7EC_act_inj {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ v, QAlgorithms.act A v = QAlgorithms.act B v) : A = B := by
  have : Matrix.toEuclideanLin A = Matrix.toEuclideanLin B := LinearMap.ext h
  exact Matrix.toEuclideanLin.injective this

lemma X7EC_projAct {n : ℕ} (S : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (v : EuclideanSpace ℂ (Fin n)) :
    QAlgorithms.act (orthogonalProjector S) v = S.starProjection v := by
  have hv : v = ∑ j, v j • (WithLp.toLp 2 (fun k => if k = j then (1 : ℂ) else 0) :
      EuclideanSpace ℂ (Fin n)) := by
    ext i
    simp [Finset.sum_apply]
  conv_rhs => rw [hv]
  rw [map_sum]
  ext i
  simp only [map_smul, QAlgorithms.act, Matrix.mulVec, dotProduct, orthogonalProjector]
  simp [Finset.sum_apply, mul_comm]


lemma X7EC_proj_entry {n : ℕ} (S : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (i j : Fin n) :
    orthogonalProjector S i j =
      inner ℂ (EuclideanSpace.single i (1 : ℂ)) (S.starProjection (EuclideanSpace.single j (1 : ℂ))) := by
  rw [EuclideanSpace.inner_single_left]
  have : (WithLp.toLp 2 (fun k => if k = j then (1 : ℂ) else 0) : EuclideanSpace ℂ (Fin n)) =
      EuclideanSpace.single j (1 : ℂ) := by
    ext k; simp
  simp [orthogonalProjector, this]

lemma X7EC_proj_herm {n : ℕ} (S : Submodule ℂ (EuclideanSpace ℂ (Fin n))) :
    (orthogonalProjector S)ᴴ = orthogonalProjector S := by
  ext i j
  rw [Matrix.conjTranspose_apply, X7EC_proj_entry, X7EC_proj_entry,
    ← Submodule.inner_starProjection_left_eq_right, ← inner_conj_symm]
  simp

lemma X7EC_proj_idem {n : ℕ} (S : Submodule ℂ (EuclideanSpace ℂ (Fin n))) :
    orthogonalProjector S * orthogonalProjector S = orthogonalProjector S := by
  apply X7EC_act_inj
  intro v
  rw [← X7EC_act_mul, X7EC_projAct, X7EC_projAct]
  exact Submodule.starProjection_eq_self_iff.mpr (Submodule.starProjection_apply_mem _ _)

lemma X7EC_adjoin_inv {n : ℕ} (G : Set (Matrix (Fin n) (Fin n) ℂ))
    (S : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (h : invariant G S) :
    invariant (Algebra.adjoin ℂ G : Set (Matrix (Fin n) (Fin n) ℂ)) S := by
  intro X hX
  induction hX using Algebra.adjoin_induction with
  | mem x hx => exact h x hx
  | algebraMap c =>
    intro v hv
    have : QAlgorithms.act (algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ) c) v = c • v := by
      ext i; simp [QAlgorithms.act, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec]
    rw [this]; exact S.smul_mem c hv
  | add x y _ _ hx hy =>
    intro v hv
    have : QAlgorithms.act (x + y) v = QAlgorithms.act x v + QAlgorithms.act y v := by
      ext i; simp [QAlgorithms.act, Matrix.add_mulVec]
    rw [this]; exact S.add_mem (hx v hv) (hy v hv)
  | mul x y _ _ hx hy =>
    intro v hv
    rw [← X7EC_act_mul]; exact hx _ (hy v hv)


lemma X7EC_adj {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (v w : EuclideanSpace ℂ (Fin n)) :
    inner ℂ v (QAlgorithms.act Aᴴ w) = inner ℂ (QAlgorithms.act A v) w := by
  change inner ℂ v (Matrix.toEuclideanLin Aᴴ w) = inner ℂ (Matrix.toEuclideanLin A v) w
  rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_inner_right]

/-- S invariant under A implies Sᗮ invariant under Aᴴ. -/
lemma X7EC_perp {n : ℕ} (S : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (A : Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ v ∈ S, QAlgorithms.act A v ∈ S) : ∀ w ∈ Sᗮ, QAlgorithms.act Aᴴ w ∈ Sᗮ := by
  intro w hw
  rw [Submodule.mem_orthogonal] at hw ⊢
  intro u hu
  rw [X7EC_adj]
  exact hw _ (h u hu)

lemma X7EC_perp' {n : ℕ} (S : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (A : Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ v ∈ Sᗮ, QAlgorithms.act A v ∈ Sᗮ) : ∀ w ∈ S, QAlgorithms.act Aᴴ w ∈ S := by
  have := X7EC_perp Sᗮ A h
  rwa [Submodule.orthogonal_orthogonal] at this

/-- S and Sᗮ invariant implies commuting with the projector. -/
lemma X7EC_comm {n : ℕ} (S : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (A : Matrix (Fin n) (Fin n) ℂ)
    (h1 : ∀ v ∈ S, QAlgorithms.act A v ∈ S) (h2 : ∀ v ∈ Sᗮ, QAlgorithms.act A v ∈ Sᗮ) :
    orthogonalProjector S * A = A * orthogonalProjector S := by
  apply X7EC_act_inj
  intro v
  rw [← X7EC_act_mul, ← X7EC_act_mul, X7EC_projAct, X7EC_projAct]
  have hA : S.starProjection (QAlgorithms.act A (v - S.starProjection v)) = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff S).mpr (h2 _ (Submodule.sub_starProjection_mem_orthogonal v))
  have hB : S.starProjection (QAlgorithms.act A (S.starProjection v)) =
      QAlgorithms.act A (S.starProjection v) :=
    Submodule.starProjection_eq_self_iff.mpr (h1 _ (Submodule.starProjection_apply_mem _ _))
  have hlin : QAlgorithms.act A (v - S.starProjection v) =
      QAlgorithms.act A v - QAlgorithms.act A (S.starProjection v) :=
    map_sub (Matrix.toEuclideanLin A) _ _
  rw [hlin, map_sub, sub_eq_zero] at hA
  rw [hA, hB]

/-- commuting with the projector implies invariance -/
lemma X7EC_comm_inv {n : ℕ} (S : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (A : Matrix (Fin n) (Fin n) ℂ)
    (h : orthogonalProjector S * A = A * orthogonalProjector S) :
    ∀ v ∈ S, QAlgorithms.act A v ∈ S := by
  intro v hv
  have hPv : QAlgorithms.act (orthogonalProjector S) v = v := by
    rw [X7EC_projAct]; exact Submodule.starProjection_eq_self_iff.mpr hv
  rw [← hPv, X7EC_act_mul, ← h, ← X7EC_act_mul, X7EC_projAct]
  exact Submodule.starProjection_apply_mem _ _

lemma X7EC_K_mem {n : ℕ} (D : LindbladData n) : driftK D ∈ extendedStarAlgebra D := by
  unfold driftK extendedStarAlgebra
  refine Subalgebra.add_mem _ (Subalgebra.smul_mem _ (Algebra.subset_adjoin (Set.mem_insert _ _)) _)
    (Subalgebra.smul_mem _ (Subalgebra.sum_mem _ fun k _ => Subalgebra.mul_mem _ ?_ ?_) _)
  · exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ (Or.inr ⟨k, rfl⟩))
  · exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ (Or.inl ⟨k, rfl⟩))

lemma X7EC_Kh {n : ℕ} (D : LindbladData n) :
    D.drift = (1 / (2 * Complex.I)) • (driftK D - (driftK D)ᴴ) := by
  have hM : (∑ k, (D.jump k)ᴴ * D.jump k)ᴴ = ∑ k, (D.jump k)ᴴ * D.jump k := by
    rw [Matrix.conjTranspose_sum]
    simp [Matrix.conjTranspose_mul]
  have hH : D.driftᴴ = D.drift := D.drift_hermitian
  unfold driftK
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul, hM, hH]
  have : star Complex.I = -Complex.I := by simp
  rw [this]
  have h2 : star (1 / 2 : ℂ) = 1 / 2 := by simp
  rw [h2, add_sub_add_right_eq_sub, ← sub_smul, smul_smul]
  have h3 : 1 / (2 * Complex.I) * (Complex.I - -Complex.I) = 1 := by
    field_simp; ring
  rw [h3, one_smul]

end QAlgorithms.Papers.Independent.Dependency50.P16

open scoped BigOperators Matrix ComplexConjugate ENNReal NNReal Matrix.Norms.L2Operator

open MeasureTheory Filter

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance 100] LieRing.ofAssociativeRing

open QAlgorithms.Papers.Independent.Dependency50.P16 in
theorem solution {n : ℕ} (hn : 2 ≤ n) (D : LindbladData n)
    (S : Submodule ℂ ((fun n : ℕ => EuclideanSpace ℂ (Fin n)) n)) :
    List.TFAE [collecting0 (driftK D) D.jump S ∧ collecting0 (driftK D) D.jump Sᗮ,
      invariant (extendedStarAlgebra D : Set ((fun n : ℕ => Matrix (Fin n) (Fin n) ℂ) n)) S,
      enclosure D S] := by
  have hHh : D.driftᴴ = D.drift := D.drift_hermitian
  tfae_have 1 → 3 := by
    rintro ⟨h1, h2⟩
    have g : ∀ T : Submodule ℂ (EuclideanSpace ℂ (Fin n)), collecting0 (driftK D) D.jump T →
        (∀ v ∈ T, QAlgorithms.act (driftK D) v ∈ T) ∧
          ∀ k, ∀ v ∈ T, QAlgorithms.act (D.jump k) v ∈ T := by
      intro T hT
      exact ⟨hT _ (Algebra.subset_adjoin (Set.mem_insert _ _)),
        fun k => hT _ (Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨k, rfl⟩))⟩
    obtain ⟨a1, b1⟩ := g S h1
    obtain ⟨a2, b2⟩ := g Sᗮ h2
    refine ⟨fun k => X7EC_comm S _ (b1 k) (b2 k), ?_⟩
    have hK := X7EC_comm S _ a1 a2
    have hKh : orthogonalProjector S * (driftK D)ᴴ = (driftK D)ᴴ * orthogonalProjector S := by
      have := congrArg Matrix.conjTranspose hK
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, X7EC_proj_herm] at this
      exact this.symm
    rw [X7EC_Kh D, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, hK, hKh]
  tfae_have 3 → 2 := by
    rintro ⟨hj, hd⟩
    apply X7EC_adjoin_inv
    rintro X (rfl | (⟨k, rfl⟩ | ⟨k, rfl⟩))
    · exact X7EC_comm_inv S _ hd
    · exact X7EC_comm_inv S _ (hj k)
    · apply X7EC_comm_inv S
      have := congrArg Matrix.conjTranspose (hj k)
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, X7EC_proj_herm] at this
      exact this.symm
  tfae_have 2 → 1 := by
    intro h2
    have hperp : invariant (extendedStarAlgebra D : Set (Matrix (Fin n) (Fin n) ℂ)) Sᗮ := by
      apply X7EC_adjoin_inv
      rintro X (rfl | (⟨k, rfl⟩ | ⟨k, rfl⟩))
      · have := X7EC_perp S D.drift (h2 _ (Algebra.subset_adjoin (Set.mem_insert _ _)))
        rwa [hHh] at this
      · have := X7EC_perp S (D.jump k)ᴴ
          (h2 _ (Algebra.subset_adjoin (Set.mem_insert_of_mem _ (Or.inr ⟨k, rfl⟩))))
        rwa [Matrix.conjTranspose_conjTranspose] at this
      · exact X7EC_perp S (D.jump k)
          (h2 _ (Algebra.subset_adjoin (Set.mem_insert_of_mem _ (Or.inl ⟨k, rfl⟩))))
    have hsub : ∀ T : Submodule ℂ (EuclideanSpace ℂ (Fin n)),
        invariant (extendedStarAlgebra D : Set (Matrix (Fin n) (Fin n) ℂ)) T →
          collecting0 (driftK D) D.jump T := by
      intro T hT
      apply X7EC_adjoin_inv
      rintro X (rfl | ⟨k, rfl⟩)
      · exact hT _ (X7EC_K_mem D)
      · exact hT _ (Algebra.subset_adjoin (Set.mem_insert_of_mem _ (Or.inl ⟨k, rfl⟩)))
    exact ⟨hsub S h2, hsub _ hperp⟩
  tfae_finish
