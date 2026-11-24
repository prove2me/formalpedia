-- Prove2me | solution 2 for WeilConjectures.exists_snf_diag_factorization_of_poly_matrix
-- status  : ACCEPTED   (prove)
-- author  : @ytako6706
-- created : 2026-11-24T05:13:44.394556+00:00
-- url     : https://prove2.me/submissions/4ce10f23-3ba3-4e55-8ddf-1f4cff3414a2

import Mathlib

open Matrix

/-- Mapped bases from Smith-normal-form preimage data for a single matrix. -/
theorem aux_bases {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (Polynomial K)) {n : ℕ}
    (snf : Module.Basis.SmithNormalForm (LinearMap.range (Matrix.toLin' M)) ι n)
    (v : Fin n → (ι → Polynomial K)) (δ : ι → Polynomial K)
    (hda : ∀ j, δ (snf.f j) = snf.a j)
    (hoff : ∀ i, (∀ j : Fin n, snf.f j ≠ i) → δ i = 0)
    (hv : ∀ j, Matrix.toLin' M (v j) = δ (snf.f j) • snf.bM (snf.f j)) :
    ∃ (bSrc bTgt : Module.Basis ι (Polynomial K) (ι → Polynomial K)),
      ∀ i, Matrix.toLin' M (bSrc i) = δ i • bTgt i := by
  classical
  -- a linear section of `(Matrix.toLin' M)` over its range, sending `bN j` to the preimage `v j`
  let s : LinearMap.range (Matrix.toLin' M) →ₗ[Polynomial K] (ι → Polynomial K) :=
    snf.bN.constr (Polynomial K) v
  have hsj : ∀ j, s (snf.bN j) = v j := fun j => by
    simp [s]
  have hcomp : (Matrix.toLin' M).comp s = (LinearMap.range (Matrix.toLin' M)).subtype := by
    refine snf.bN.ext (fun j => ?_)
    simp only [LinearMap.comp_apply, hsj, Submodule.subtype_apply]
    rw [snf.snf j, hv j, hda j]
  have hs : ∀ x : LinearMap.range (Matrix.toLin' M), (Matrix.toLin' M) (s x) = x := fun x =>
    LinearMap.congr_fun hcomp x
  -- a finite basis of the kernel (PID)
  obtain ⟨k, bK⟩ :=
    Submodule.basisOfPid (Pi.basisFun (Polynomial K) ι) (LinearMap.ker (Matrix.toLin' M))
  -- the splitting `ker (Matrix.toLin' M) × range (Matrix.toLin' M) ≃ K[X]^ι`, `(y, z) ↦ y + s z`
  let T : (LinearMap.ker (Matrix.toLin' M) × LinearMap.range (Matrix.toLin' M)) →ₗ[Polynomial K] (ι → Polynomial K) :=
    (LinearMap.ker (Matrix.toLin' M)).subtype.coprod s
  have hTinj : Function.Injective T := by
    refine (injective_iff_map_eq_zero T).mpr ?_
    rintro ⟨y, z⟩ h
    have h' : (y : ι → Polynomial K) + s z = 0 := by
      simpa [T, LinearMap.coprod_apply] using h
    have hz : (z : ι → Polynomial K) = 0 := by
      have := congrArg (Matrix.toLin' M) h'
      rw [map_add, hs z, LinearMap.mem_ker.mp y.2, zero_add, map_zero] at this
      exact this
    have hz' : z = 0 := Subtype.ext hz
    have hy : (y : ι → Polynomial K) = 0 := by
      rw [hz', map_zero, add_zero] at h'
      exact h'
    exact Prod.ext (Subtype.ext hy) hz'
  have hTsurj : Function.Surjective T := by
    intro x
    have hmem : x - s ((Matrix.toLin' M).rangeRestrict x) ∈ LinearMap.ker (Matrix.toLin' M) := by
      rw [LinearMap.mem_ker, map_sub, hs]
      simp
    refine ⟨(⟨_, hmem⟩, (Matrix.toLin' M).rangeRestrict x), ?_⟩
    simp [T, LinearMap.coprod_apply]
  let e := LinearEquiv.ofBijective T ⟨hTinj, hTsurj⟩
  let B : Module.Basis (Fin k ⊕ Fin n) (Polynomial K) (ι → Polynomial K) :=
    (bK.prod snf.bN).map e
  have hBl : ∀ a, B (Sum.inl a) = (bK a : ι → Polynomial K) := fun a => by
    simp only [B, e]
    simp only [Module.Basis.map_apply]
    erw [LinearEquiv.ofBijective_apply]
    simp [T, LinearMap.coprod_apply]
  have hBr : ∀ j, B (Sum.inr j) = v j := fun j => by
    simp only [B, e]
    simp only [Module.Basis.map_apply]
    erw [LinearEquiv.ofBijective_apply]
    simp [T, LinearMap.coprod_apply, hsj]
  -- cardinality bookkeeping
  have hcard : Fintype.card ι = k + n := by
    have h1 := Module.finrank_eq_card_basis B
    have h2 := Module.finrank_eq_card_basis (Pi.basisFun (Polynomial K) ι)
    simp only [Fintype.card_sum, Fintype.card_fin] at h1
    omega
  let eOn : Set.range snf.f ≃ Fin n := (Equiv.ofInjective snf.f snf.f.injective).symm
  have hOnCard : Fintype.card (Set.range snf.f) = n := by
    rw [Fintype.card_congr eOn, Fintype.card_fin]
  have hOffCard : Fintype.card {i // i ∉ Set.range snf.f} = k := by
    rw [Fintype.card_subtype_compl, hOnCard, hcard]
    omega
  let eOff : {i // i ∉ Set.range snf.f} ≃ Fin k := Fintype.equivFinOfCardEq hOffCard
  let E : ι ≃ Fin k ⊕ Fin n :=
    ((Equiv.sumCompl (fun i => i ∈ Set.range snf.f)).symm.trans
      (Equiv.sumComm _ _)).trans (Equiv.sumCongr eOff eOn)
  have key : ∀ x, (Matrix.toLin' M) (B x) = δ (E.symm x) • snf.bM (E.symm x) := by
    rintro (a | j)
    · have hE : E.symm (Sum.inl a) = (eOff.symm a : ι) := by
        simp [E]
      have hnot : (∀ j : Fin n, snf.f j ≠ (eOff.symm a : ι)) := by
        intro j hj
        exact (eOff.symm a).2 ⟨j, hj⟩
      rw [hBl, LinearMap.mem_ker.mp (bK a).2, hE, hoff _ hnot, zero_smul]
    · have hE : E.symm (Sum.inr j) = snf.f j := by
        simp [E, eOn]
      rw [hBr, hE, hv j]
  refine ⟨B.reindex E.symm, snf.bM, fun i => ?_⟩
  have := key (E i)
  simpa [Module.Basis.reindex_apply] using this

/-- Every square matrix over `K[X]` is equivalent to a diagonal matrix. -/
theorem exists_diag {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (Polynomial K)) :
    ∃ δ : ι → Polynomial K, ∃ P Q : Matrix ι ι (Polynomial K),
      IsUnit P.det ∧ IsUnit Q.det ∧ P * M * Q = Matrix.diagonal δ := by
  classical
  obtain ⟨n, snf⟩ :=
    Submodule.smithNormalForm (Pi.basisFun (Polynomial K) ι) (LinearMap.range (Matrix.toLin' M))
  let v : Fin n → (ι → Polynomial K) := fun j => (LinearMap.mem_range.mp (snf.bN j).2).choose
  have hvv : ∀ j, Matrix.toLin' M (v j) = snf.bN j := fun j =>
    (LinearMap.mem_range.mp (snf.bN j).2).choose_spec
  let δ : ι → Polynomial K := fun i => if h : ∃ j, snf.f j = i then snf.a h.choose else 0
  have hda : ∀ j, δ (snf.f j) = snf.a j := by
    intro j
    have h : ∃ j', snf.f j' = snf.f j := ⟨j, rfl⟩
    simp only [δ, dif_pos h]
    rw [snf.f.injective h.choose_spec]
  have hoff : ∀ i, (∀ j : Fin n, snf.f j ≠ i) → δ i = 0 := by
    intro i hi
    have : ¬ ∃ j, snf.f j = i := fun ⟨j, hj⟩ => hi j hj
    simp only [δ, dif_neg this]
  have hv : ∀ j, Matrix.toLin' M (v j) = δ (snf.f j) • snf.bM (snf.f j) := by
    intro j
    rw [hvv, snf.snf j, hda j]
  obtain ⟨bSrc, bTgt, hb⟩ := aux_bases M snf v δ hda hoff hv
  have hmat : LinearMap.toMatrix bSrc bTgt (Matrix.toLin' M) = Matrix.diagonal δ := by
    ext i j
    rw [LinearMap.toMatrix_apply, hb j, map_smul, bTgt.repr_self, Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  refine ⟨δ, ?_⟩
  set E := Pi.basisFun (Polynomial K) ι
  have hM : E.toMatrix bTgt * Matrix.diagonal δ * bSrc.toMatrix E = M := by
    rw [← hmat, basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix,
      LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']
  refine ⟨bTgt.toMatrix E, E.toMatrix bSrc, ?_, ?_, ?_⟩
  · exact Matrix.isUnit_det_of_left_inverse (Module.Basis.toMatrix_mul_toMatrix_flip E bTgt)
  · exact Matrix.isUnit_det_of_left_inverse (Module.Basis.toMatrix_mul_toMatrix_flip bSrc E)
  · conv_lhs => rw [← hM]
    simp only [Matrix.mul_assoc, Module.Basis.toMatrix_mul_toMatrix_flip, Matrix.mul_one]
    rw [← Matrix.mul_assoc, Module.Basis.toMatrix_mul_toMatrix_flip, Matrix.one_mul]

/-- Transpose-symmetric choice of a diagonalizing factorization. -/
theorem solution
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι] :
    ∃ (d : Matrix ι ι (Polynomial K) → (ι → Polynomial K)),
      (∀ M i, d M i = d M.transpose i) ∧
      (∀ M, ∃ (P Q : Matrix ι ι (Polynomial K)),
        IsUnit P.det ∧ IsUnit Q.det ∧
          P * M * Q = Matrix.diagonal (d M)) := by
  classical
  -- the property of a diagonal `δ` relative to a set of matrices
  let good : Set (Matrix ι ι (Polynomial K)) → (ι → Polynomial K) → Prop := fun S δ =>
    ∀ N ∈ S, ∃ (P Q : Matrix ι ι (Polynomial K)),
      IsUnit P.det ∧ IsUnit Q.det ∧ P * N * Q = Matrix.diagonal δ
  have hex : ∀ M : Matrix ι ι (Polynomial K), ∃ δ, good {M, M.transpose} δ := by
    intro M
    obtain ⟨δ, P, Q, hP, hQ, h⟩ := exists_diag M
    refine ⟨δ, ?_⟩
    rintro N (rfl | rfl)
    · exact ⟨P, Q, hP, hQ, h⟩
    · refine ⟨Q.transpose, P.transpose, by rwa [Matrix.det_transpose],
        by rwa [Matrix.det_transpose], ?_⟩
      rw [← Matrix.transpose_mul, ← Matrix.transpose_mul, ← Matrix.mul_assoc, h,
        Matrix.diagonal_transpose]
  let d : Matrix ι ι (Polynomial K) → (ι → Polynomial K) := fun M =>
    Classical.epsilon (good {M, M.transpose})
  refine ⟨d, ?_, ?_⟩
  · intro M i
    have hset : ({M.transpose, M.transpose.transpose} : Set (Matrix ι ι (Polynomial K))) =
        {M, M.transpose} := by
      rw [Matrix.transpose_transpose, Set.pair_comm]
    simp only [d, hset]
  · intro M
    exact Classical.epsilon_spec (hex M) M (Set.mem_insert _ _)
