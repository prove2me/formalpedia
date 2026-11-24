-- Prove2me | solution 2 for WeilConjectures.exists_mapped_bases_of_snf_preimage_family
-- status  : ACCEPTED   (prove)
-- author  : @ytako6706
-- created : 2026-11-24T05:07:33.468714+00:00
-- url     : https://prove2.me/submissions/eb479b50-3a86-4c0c-8aec-ed4b47ff3abc

import Mathlib

theorem solution
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (d : Matrix ι ι (Polynomial K) → (ι → Polynomial K))
    (hpre : ∀ M, ∃ (n : ℕ)
      (snf : Module.Basis.SmithNormalForm
        (LinearMap.range (Matrix.toLin' M)) ι n)
      (v : Fin n → (ι → Polynomial K)),
      (∀ j, d M (snf.f j) = snf.a j) ∧
      (∀ i, (∀ j : Fin n, snf.f j ≠ i) → d M i = 0) ∧
      (∀ j, Matrix.toLin' M (v j) = d M (snf.f j) • snf.bM (snf.f j))) :
    ∀ M, ∃ (bSrc bTgt : Module.Basis ι (Polynomial K) (ι → Polynomial K)),
      ∀ i, Matrix.toLin' M (bSrc i) = d M i • bTgt i := by
  classical
  intro M
  obtain ⟨n, snf, v, hda, hoff, hv⟩ := hpre M
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
  have key : ∀ x, (Matrix.toLin' M) (B x) = d M (E.symm x) • snf.bM (E.symm x) := by
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
