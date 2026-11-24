-- Prove2me | solution 1 for WeilConjectures.snf_diag_eq_transpose_of_unit_equiv
-- status  : ACCEPTED   (disprove)
-- author  : @ytako6706
-- created : 2026-11-24T05:11:14.2978+00:00
-- url     : https://prove2.me/submissions/f38c2364-1333-4749-9dcc-96339df321af

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

/-- Counterexample: an unnormalized diagonal assignment can order the diagonal of
`M₀ = !![0, 1; 0, 0]` and of its transpose differently. -/
theorem solution :
    ¬ (∀ {K ι : Type} [Field K] [Fintype ι] [DecidableEq ι]
      (d : Matrix ι ι (Polynomial K) → (ι → Polynomial K))
      (hfac : ∀ M, ∃ (P Q : Matrix ι ι (Polynomial K)),
        IsUnit P.det ∧ IsUnit Q.det ∧
          P * M * Q = Matrix.diagonal (d M)),
      ∀ M i, d M i = d M.transpose i) := by
  classical
  intro h
  let M0 : Matrix (Fin 2) (Fin 2) (Polynomial ℚ) := !![0, 1; 0, 0]
  have hne : M0ᵀ ≠ M0 := by
    intro heq
    have := congrFun (congrFun heq 0) 1
    simp [M0] at this
  let d : Matrix (Fin 2) (Fin 2) (Polynomial ℚ) → Fin 2 → Polynomial ℚ := fun M =>
    if M = M0 then ![1, 0] else if M = M0ᵀ then ![0, 1] else (exists_diag M).choose
  have hswap : IsUnit (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (Polynomial ℚ)).det := by
    rw [Matrix.det_fin_two_of]
    simp
  have hfac : ∀ M, ∃ (P Q : Matrix (Fin 2) (Fin 2) (Polynomial ℚ)),
      IsUnit P.det ∧ IsUnit Q.det ∧ P * M * Q = Matrix.diagonal (d M) := by
    intro M
    by_cases h1 : M = M0
    · refine ⟨1, !![0, 1; 1, 0], by simp, hswap, ?_⟩
      have hd : d M = ![1, 0] := by simp only [d, if_pos h1]
      rw [hd, h1]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [M0, Matrix.mul_apply, Fin.sum_univ_two]
    · by_cases h2 : M = M0ᵀ
      · refine ⟨1, !![0, 1; 1, 0], by simp, hswap, ?_⟩
        have hd : d M = ![0, 1] := by simp only [d, if_neg h1, if_pos h2]
        rw [hd, h2]
        ext i j
        fin_cases i <;> fin_cases j <;> simp [M0, Matrix.mul_apply, Fin.sum_univ_two]
      · have hd : d M = (exists_diag M).choose := by simp only [d, if_neg h1, if_neg h2]
        rw [hd]
        exact (exists_diag M).choose_spec
  have key := h (K := ℚ) (ι := Fin 2) d hfac M0 0
  have hd0 : d M0 = ![1, 0] := by simp [d]
  have hd1 : d M0ᵀ = ![0, 1] := by simp [d, hne]
  rw [hd0, hd1] at key
  simp at key
