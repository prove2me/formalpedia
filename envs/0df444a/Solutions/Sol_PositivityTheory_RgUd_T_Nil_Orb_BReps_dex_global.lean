-- Prove2me | solution 1 for PositivityTheory.RgUd.T.Nil.Orb.BReps.dex_global
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:41:13.503399+00:00
-- url     : https://prove2.me/submissions/03c29c5e-8867-42b6-9fc7-f3ab89812d5e

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_CentralizerRepresentatives_DexBlockFrame
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_CentralizerRepresentatives_DexGlobal
import Theorems.Thm_PositivityTheory_RgUd_T_Nil_Orb_BReps_dex_block_frame


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Orb PositivityTheory.RgUd.T.Nil.Orb.BReps
open Module
variable {k : Type} [Field k]
namespace PositivityTheory.RgUd.T.Nil.Orb.BReps
theorem _root_.solution {R : Type} [CommRing R] [Algebra k R] [FiniteDimensional k R] [IsReduced R]
    {V : Type} [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V] [FiniteDimensional k V] :
    ∃ (M : Type) (_ : Fintype M) (L : M → Type) (_ : ∀ m, Fintype (L m)) (_ : ∀ m, Nonempty (L m))
      (Rc : R → (m : M) → L m → L m → k) (o : (m : M) → L m → k),
      ∀ N : V →ₗ[R] V, IsNilpotent N → ∀ v : V,
        ∃ (ι : M → Type) (_ : ∀ m, Fintype (ι m)) (l s : (m : M) → ι m → ℕ)
          (β : Basis (Σ m, L m × (Σ a : ι m, Fin (l m a))) k V),
          (∀ m a, 0 < l m a) ∧ (∀ m a, s m a ≤ l m a) ∧
          (∀ (z : R) m (p : L m) (j : Σ a : ι m, Fin (l m a)),
            z • β ⟨m, (p, j)⟩ = ∑ q, Rc z m p q • β ⟨m, (q, j)⟩) ∧
          (∀ m (p : L m) (a : ι m) (i : Fin (l m a)), N (β ⟨m, (p, ⟨a, i⟩)⟩) =
            if h : (i : ℕ) + 1 < l m a then β ⟨m, (p, ⟨a, ⟨i + 1, h⟩⟩)⟩ else 0) ∧
          v = ∑ m, ∑ p, ∑ a, (if h : s m a < l m a then o m p • β ⟨m, (p, ⟨a, ⟨s m a, h⟩⟩)⟩ else 0) ∧
          ∀ A : V →ₗ[R] V, A ∘ₗ N = N ∘ₗ A → ∀ m (p : L m) (a : ι m) (i : Fin (l m a)), (i : ℕ) < s m a →
            β.repr (A v) ⟨m, (p, ⟨a, i⟩)⟩ = 0 := by
  haveI : IsArtinianRing R := IsArtinianRing.of_finite k R
  classical
  let M := MaximalSpectrum R
  letI : Fintype M := Fintype.ofFinite M
  have hfin : ∀ m : M, Module.Finite k (R ⧸ m.asIdeal) := fun m =>
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ k m.asIdeal).toLinearMap Ideal.Quotient.mk_surjective
  let L : M → Type := fun m => Fin (finrank k (R ⧸ m.asIdeal))
  let b : ∀ m : M, Basis (L m) k (R ⧸ m.asIdeal) := fun m => by
    haveI := hfin m
    exact Module.finBasis k _
  have hne : ∀ m, Nonempty (L m) := fun m => by
    haveI := hfin m
    haveI : Nontrivial (R ⧸ m.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr m.isMaximal.ne_top
    exact ⟨⟨0, Module.finrank_pos⟩⟩
  refine ⟨M, inferInstance, L, fun m => inferInstance, hne,
    fun z m p q => (b m).repr (Ideal.Quotient.mk _ z * b m p) q, fun m p => (b m).repr 1 p, ?_⟩
  intro N hN v

  let e : M → R := fun m => (IsArtinianRing.equivPi R).symm (Pi.single m 1)
  have he : ∀ m, IsArtinianRing.equivPi R (e m) = Pi.single m 1 := fun m => AlgEquiv.apply_symm_apply _ _
  have hE1 : ∀ m, ∀ z ∈ m.asIdeal, z * e m = 0 := by
    intro m z hz
    apply (IsArtinianRing.equivPi R).injective
    funext m'
    rw [map_mul, he, map_zero, Pi.mul_apply, Pi.zero_apply]
    by_cases h : m' = m
    · subst h
      rw [Pi.single_eq_same, mul_one, IsArtinianRing.equivPi_apply]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hz
    · rw [Pi.single_eq_of_ne h, mul_zero]
  have hE2 : ∑ m, e m = 1 := by
    apply (IsArtinianRing.equivPi R).injective
    rw [map_sum, map_one]
    funext m'
    rw [Finset.sum_apply, Finset.sum_eq_single m']
    · rw [he, Pi.single_eq_same, Pi.one_apply]
    · intro x _ hx
      rw [he, Pi.single_eq_of_ne (Ne.symm hx)]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hE3 : ∀ m m', m' ≠ m → e m' * e m = 0 := by
    intro m m' hmm
    apply (IsArtinianRing.equivPi R).injective
    funext x
    rw [map_mul, he, he, map_zero, Pi.mul_apply, Pi.zero_apply]
    by_cases h : x = m
    · subst h
      rw [Pi.single_eq_of_ne hmm.symm, zero_mul]
    · rw [Pi.single_eq_of_ne h, mul_zero]
  have hE4 : ∀ m, e m * e m = e m := by
    intro m
    apply (IsArtinianRing.equivPi R).injective
    funext x
    rw [map_mul, he, Pi.mul_apply]
    by_cases h : x = m
    · subst h
      rw [Pi.single_eq_same, mul_one]
    · rw [Pi.single_eq_of_ne h, mul_zero]

  let Vm : M → Submodule R V := fun m => LinearMap.range (LinearMap.lsmul R V (e m))
  have hself : ∀ m (y : V), e m • y ∈ Vm m := fun m y => LinearMap.mem_range_self _ y
  have hfix : ∀ m, ∀ y ∈ Vm m, e m • y = y := by
    rintro m y ⟨w, rfl⟩
    simp only [LinearMap.lsmul_apply, smul_smul, hE4]
  have hkill : ∀ m m', m' ≠ m → ∀ y ∈ Vm m, e m' • y = 0 := by
    rintro m m' hmm y ⟨w, rfl⟩
    simp only [LinearMap.lsmul_apply, smul_smul, hE3 m m' hmm, zero_smul]
  have htor : ∀ m, ∀ z ∈ m.asIdeal, ∀ y : Vm m, z • y = 0 := by
    intro m z hz y
    apply Subtype.ext
    rw [Submodule.coe_smul, Submodule.coe_zero, ← hfix m y.1 y.2, smul_smul, hE1 m z hz, zero_smul]
  haveI hVfin : ∀ m, FiniteDimensional k (Vm m) := fun m =>
    Module.Finite.of_injective ((Vm m).subtype.restrictScalars k) Subtype.val_injective
  have hNm : ∀ m, ∀ y ∈ Vm m, N y ∈ Vm m := by
    rintro m y ⟨w, rfl⟩
    rw [LinearMap.lsmul_apply, map_smul]
    exact hself m (N w)
  have hpow : ∀ m (j : ℕ) (y : Vm m), (((N.restrict (hNm m)) ^ j) y : V) = (N ^ j) y := by
    intro m j
    induction j with
    | zero => intro y; rfl
    | succ j ih =>
      intro y
      rw [pow_succ, Module.End.mul_apply, ih, pow_succ, Module.End.mul_apply]
      rfl
  have hNnil : ∀ m, IsNilpotent (N.restrict (hNm m)) := by
    intro m
    obtain ⟨r, hr⟩ := hN
    refine ⟨r, LinearMap.ext fun y => Subtype.ext ?_⟩
    rw [hpow, hr]
    rfl
  have hblk (m : M) := dex_block_frame m.asIdeal (b m) (W := Vm m) (htor m) (N.restrict (hNm m)) (hNnil m)
    ⟨e m • v, hself m v⟩
  choose ι fι l s βm hl hs hZ hN' hv hA using hblk

  have hInt : DirectSum.IsInternal (fun m => (Vm m).restrictScalars k) := by
    apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    · rw [iSupIndep_def]
      intro m
      let φ : V →ₗ[k] V := (LinearMap.lsmul R V (e m)).restrictScalars k
      have hle : (⨆ (j) (_ : j ≠ m), (Vm j).restrictScalars k) ≤ LinearMap.ker φ :=
        iSup₂_le fun j hj y hy => by
          rw [LinearMap.mem_ker]
          exact hkill j m (Ne.symm hj) y hy
      rw [Submodule.disjoint_def]
      intro y hy hy'
      have h1 := hle hy'
      rw [LinearMap.mem_ker] at h1
      rw [← hfix m y hy]
      exact h1
    · refine eq_top_iff.mpr fun y _ => ?_
      have hy : y = ∑ m, e m • y := by rw [← Finset.sum_smul, hE2, one_smul]
      rw [hy]
      exact Submodule.sum_mem _ fun m _ => Submodule.mem_iSup_of_mem m (hself m y)
  let eqv : ∀ m, (Vm m) ≃ₗ[k] ((Vm m).restrictScalars k) := fun m =>
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let β := hInt.collectedBasis (fun m => (βm m).map (eqv m))
  have hβ : ∀ m j, β ⟨m, j⟩ = ((βm m j : Vm m) : V) := by
    intro m j
    rw [DirectSum.IsInternal.collectedBasis_coe]
    rfl
  refine ⟨ι, fι, l, s, β, hl, hs, ?_, ?_, ?_, ?_⟩
  · intro z m p j
    rw [hβ, ← Submodule.coe_smul, hZ m z p j, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [hβ]
    rfl
  · intro m p a i
    rw [hβ]
    have : N ((βm m (p, ⟨a, i⟩) : Vm m) : V) = ((N.restrict (hNm m) (βm m (p, ⟨a, i⟩)) : Vm m) : V) := rfl
    rw [this, hN' m p a i]
    split_ifs with h
    · rw [hβ]
    · rfl
  · have hvs : v = ∑ m, e m • v := by rw [← Finset.sum_smul, hE2, one_smul]
    conv_lhs => rw [hvs]
    refine Finset.sum_congr rfl fun m _ => ?_
    have h1 : e m • v = ((⟨e m • v, hself m v⟩ : Vm m) : V) := rfl
    rw [h1, hv m, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Submodule.coe_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    split_ifs with h
    · rw [hβ]
      rfl
    · rfl
  · intro A hAN m p a i hi
    have hAm : ∀ m, ∀ y ∈ Vm m, A y ∈ Vm m := by
      rintro m y ⟨w, rfl⟩
      rw [LinearMap.lsmul_apply, map_smul]
      exact hself m (A w)
    have hvs : v = ∑ m, e m • v := by rw [← Finset.sum_smul, hE2, one_smul]
    have hAv : A v = ∑ m', ((A.restrict (hAm m') ⟨e m' • v, hself m' v⟩ : Vm m') : V) := by
      conv_lhs => rw [hvs]
      rw [map_sum]
      rfl
    rw [hAv, map_sum, Finsupp.finsetSum_apply]
    refine Finset.sum_eq_zero fun m' _ => ?_
    by_cases hmm : m' = m
    · subst hmm
      have hc : A.restrict (hAm m') ∘ₗ N.restrict (hNm m') = N.restrict (hNm m') ∘ₗ A.restrict (hAm m') := by
        refine LinearMap.ext fun y => Subtype.ext ?_
        exact LinearMap.congr_fun hAN y.1
      have key := DirectSum.IsInternal.collectedBasis_repr_of_mem hInt (fun m => (βm m).map (eqv m))
        (x := ((A.restrict (hAm m') ⟨e m' • v, hself m' v⟩ : Vm m') : V)) (a := (p, ⟨a, i⟩)) (Subtype.mem _)
      refine key.trans ?_
      rw [Basis.map_repr]
      exact hA m' (A.restrict (hAm m')) hc p a i hi
    · exact DirectSum.IsInternal.collectedBasis_repr_of_mem_ne hInt _ hmm (Subtype.mem _)
end PositivityTheory.RgUd.T.Nil.Orb.BReps
