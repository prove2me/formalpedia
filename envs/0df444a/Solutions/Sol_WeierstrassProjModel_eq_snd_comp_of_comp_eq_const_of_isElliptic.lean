-- Prove2me | solution 1 for WeierstrassProjModel.eq_snd_comp_of_comp_eq_const_of_isElliptic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/0ff106ed-1cac-57b2-90aa-1d2d2b181327

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Theorems.Thm_AlgebraicGeometry_exists_eq_snd_comp_of_comp_eq_const_of_isProper
import Theorems.Thm_WeierstrassProjModel_isProper_and_isIntegral_and_isReduced_selfPullback_pullback_snd_of_baseChangeIso
import Theorems.Thm_WeierstrassProjModel_projModelStrCR_isProper
import Theorems.Thm_WeierstrassProjModel_projModel_pullback_iso_baseChange
import Theorems.Thm_WeierstrassProjModel_bijective_appTop_pullback_snd_projModelStrCR
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_eq_snd_comp_of_comp_eq_const_of_isElliptic
p2m_attr_erase "instance" "WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType"
p2m_attr_erase "simp" "WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X"

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel

attribute [local instance] MvPolynomial.gradedAlgebra

namespace K1cAux

open TopologicalSpace

theorem comp_eq_id_of_comp_eq_id_of_bijective {A B : CommRingCat.{u}} (a : A ⟶ B) (b : B ⟶ A)
    (h : a ≫ b = 𝟙 A) (ha : Function.Bijective a) : b ≫ a = 𝟙 B := by
  haveI : IsIso a := (ConcreteCategory.isIso_iff_bijective a).mpr ha
  have hb : b = inv a := by
    calc b = (inv a ≫ a) ≫ b := by simp
      _ = inv a ≫ (a ≫ b) := Category.assoc _ _ _
      _ = inv a := by rw [h, Category.comp_id]
  rw [hb, IsIso.inv_hom_id]

theorem eq_comp_of_isClosedMap_of_bijective_app {X S Y : Scheme.{u}} (p : X ⟶ S) (σ : S ⟶ X)
    (hσ : σ ≫ p = 𝟙 S) (hp : IsClosedMap p.base)
    (hΓ : ∀ U : S.Opens, IsAffineOpen U → Function.Bijective (p ∣_ U).appTop)
    (f : X ⟶ Y) (hf : ∀ x : X, f.base x = f.base (σ.base (p.base x))) :
    f = p ≫ σ ≫ f := by

  have hσp : ∀ s : S, p.base (σ.base s) = s := fun s => by
    have := congrArg (fun g => g.base s) hσ
    simpa using this

  have hloc : ∀ x : X, ∃ W : X.Opens, x ∈ W ∧ W.ι ≫ f = W.ι ≫ p ≫ σ ≫ f := by
    intro x
    set s : S := p.base x with hs
    set y : Y := f.base (σ.base s) with hy

    obtain ⟨U, hUaff, hyU, -⟩ := exists_isAffineOpen_mem_and_subset (X := Y) (x := y) (U := ⊤) trivial

    have hZ : IsClosed ((f ⁻¹ᵁ U : X.Opens) : Set X)ᶜ := (f ⁻¹ᵁ U).isOpen.isClosed_compl
    have hpZ : IsClosed (p.base '' ((f ⁻¹ᵁ U : X.Opens) : Set X)ᶜ) := hp _ hZ
    have hs_notMem : s ∉ p.base '' ((f ⁻¹ᵁ U : X.Opens) : Set X)ᶜ := by
      rintro ⟨x', hx', hx's⟩
      apply hx'
      show f.base x' ∈ (U : Set Y)
      rw [hf x', hx's]
      exact hyU

    let S₀ : S.Opens := ⟨(p.base '' ((f ⁻¹ᵁ U : X.Opens) : Set X)ᶜ)ᶜ, hpZ.isOpen_compl⟩
    have hsS₀ : s ∈ S₀ := hs_notMem
    obtain ⟨S₁, hS₁aff, hsS₁, hS₁S₀⟩ := exists_isAffineOpen_mem_and_subset (X := S) (x := s) (U := S₀) hsS₀

    refine ⟨p ⁻¹ᵁ S₁, by simpa [← hs] using hsS₁, ?_⟩
    have hWU : p ⁻¹ᵁ S₁ ≤ f ⁻¹ᵁ U := by
      intro x' hx'
      by_contra hcon
      have : p.base x' ∈ p.base '' ((f ⁻¹ᵁ U : X.Opens) : Set X)ᶜ := ⟨x', hcon, rfl⟩
      exact hS₁S₀ hx' this
    have hσW : S₁ ≤ σ ⁻¹ᵁ (p ⁻¹ᵁ S₁) := by
      intro s' hs'
      show p.base (σ.base s') ∈ (S₁ : Set S)
      rw [hσp]; exact hs'

    let fW : (↑(p ⁻¹ᵁ S₁) : Scheme.{u}) ⟶ ↑U := f.resLE U (p ⁻¹ᵁ S₁) hWU
    let pW : (↑(p ⁻¹ᵁ S₁) : Scheme.{u}) ⟶ ↑S₁ := p ∣_ S₁
    let σW : (↑S₁ : Scheme.{u}) ⟶ ↑(p ⁻¹ᵁ S₁) := σ.resLE (p ⁻¹ᵁ S₁) S₁ hσW
    haveI : IsAffine (↑U : Scheme.{u}) := hUaff

    have hσpW : σW ≫ pW = 𝟙 _ := by
      rw [← cancel_mono S₁.ι]
      simp only [Category.assoc, Category.id_comp, pW, morphismRestrict_ι, σW]
      rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, hσ, Category.comp_id]

    have hpWbij : Function.Bijective pW.appTop := hΓ S₁ hS₁aff

    have hid : σW.appTop ≫ pW.appTop = 𝟙 _ := by
      have h1 : pW.appTop ≫ σW.appTop = 𝟙 _ := by
        rw [← Scheme.Hom.comp_appTop, hσpW]; simp
      exact comp_eq_id_of_comp_eq_id_of_bijective _ _ h1 hpWbij

    have hfW : fW = pW ≫ σW ≫ fW := by
      apply ext_of_isAffine
      simp only [Scheme.Hom.comp_appTop]
      rw [Category.assoc, hid, Category.comp_id]

    calc (p ⁻¹ᵁ S₁).ι ≫ f = fW ≫ U.ι := (f.resLE_comp_ι hWU).symm
      _ = (pW ≫ σW ≫ fW) ≫ U.ι := by rw [← hfW]
      _ = pW ≫ σW ≫ (p ⁻¹ᵁ S₁).ι ≫ f := by simp only [Category.assoc, fW, Scheme.Hom.resLE_comp_ι]
      _ = pW ≫ S₁.ι ≫ σ ≫ f := by simp only [σW, ← Category.assoc, Scheme.Hom.resLE_comp_ι]
      _ = (p ⁻¹ᵁ S₁).ι ≫ p ≫ σ ≫ f := by rw [← Category.assoc, show pW ≫ S₁.ι = (p ⁻¹ᵁ S₁).ι ≫ p from morphismRestrict_ι p S₁, Category.assoc]

  choose W hW using hloc
  have hcov : IsOpenCover W := by
    rw [IsOpenCover, eq_top_iff]
    intro x _
    exact Opens.mem_iSup.mpr ⟨x, (hW x).1⟩
  exact Scheme.Cover.hom_ext (X.openCoverOfIsOpenCover W hcov) _ _ fun x => by
    first | simpa using (hW x).2 | (have h_1 := (hW x).2; simp at h_1; exact h_1) | (have h_1 := (hW x).2; simp at h_1 ⊢; exact h_1) | exact ((hW x).2)

theorem bijective_comp {A B C : CommRingCat.{u}} (a : A ⟶ B) (b : B ⟶ C)
    (ha : Function.Bijective a) (hb : Function.Bijective b) : Function.Bijective (a ≫ b) := by
  have hab : ⇑(ConcreteCategory.hom (a ≫ b)) = ⇑(ConcreteCategory.hom b) ∘ ⇑(ConcreteCategory.hom a) := by
    funext t; exact ConcreteCategory.comp_apply a b t
  rw [hab]; exact hb.comp ha

theorem bijective_appTop_of_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] : Function.Bijective f.appTop := by
  have h1 : f.appTop ≫ (inv f).appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, IsIso.inv_hom_id, Scheme.Hom.id_appTop]
  have h2 : (inv f).appTop ≫ f.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, IsIso.hom_inv_id, Scheme.Hom.id_appTop]
  haveI : IsIso f.appTop := ⟨⟨(inv f).appTop, h1, h2⟩⟩
  exact ConcreteCategory.bijective_of_isIso _

theorem bijective_appTop_snd_restrict_of {R : Type u} [CommRing R] {E : Scheme.{u}}
    (p : E ⟶ Spec (CommRingCat.of R))
    (hH0 : ∀ (S : Type u) [CommRing S] [Algebra R S],
      Function.Bijective (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap R S)))).appTop)
    (U : E.Opens) (hU : IsAffineOpen U) :
    Function.Bijective ((pullback.snd p p) ∣_ U).appTop := by

  let S : Type u := ↑(Γ(E, U))
  let ψ : CommRingCat.of R ⟶ Γ(E, U) := Spec.preimage (hU.isoSpec.inv ≫ U.ι ≫ p)
  letI : Algebra R S := ψ.hom.toAlgebra
  have hb : Spec.map (CommRingCat.ofHom (algebraMap R S)) = hU.isoSpec.inv ≫ U.ι ≫ p := by
    rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom, Spec.map_preimage]
  have hbij := hH0 S
  generalize Spec.map (CommRingCat.ofHom (algebraMap R S)) = b at hbij hb
  subst hb

  have sqA : IsPullback ((pullback.snd p p) ∣_ U) (((pullback.snd p p) ⁻¹ᵁ U).ι ≫ pullback.fst p p)
      (U.ι ≫ p) p :=
    (isPullback_morphismRestrict (pullback.snd p p) U).paste_vert (IsPullback.of_hasPullback p p).flip

  have sqA' : IsPullback ((pullback.snd p p) ∣_ U ≫ hU.isoSpec.hom) (((pullback.snd p p) ⁻¹ᵁ U).ι ≫ pullback.fst p p)
      (hU.isoSpec.inv ≫ U.ι ≫ p) p := by
    refine sqA.of_iso (Iso.refl _) hU.isoSpec (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · rw [Iso.refl_hom, Category.id_comp]
    · simp
    · rw [Iso.refl_hom, Category.comp_id, Iso.hom_inv_id_assoc]
    · simp
  have sqB : IsPullback (pullback.snd p (hU.isoSpec.inv ≫ U.ι ≫ p)) (pullback.fst p (hU.isoSpec.inv ≫ U.ι ≫ p))
      (hU.isoSpec.inv ≫ U.ι ≫ p) p :=
    (IsPullback.of_hasPullback _ _).flip
  have hι : (sqA'.isoIsPullback _ _ sqB).hom ≫ pullback.snd p (hU.isoSpec.inv ≫ U.ι ≫ p) =
      (pullback.snd p p) ∣_ U ≫ hU.isoSpec.hom :=
    sqA'.isoIsPullback_hom_fst _ _ sqB
  have heq : (pullback.snd p p) ∣_ U =
      ((sqA'.isoIsPullback _ _ sqB).hom ≫ pullback.snd p (hU.isoSpec.inv ≫ U.ι ≫ p)) ≫ hU.isoSpec.inv := by
    rw [hι, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [heq, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop]
  exact bijective_comp _ _ (bijective_appTop_of_isIso _)
    (bijective_comp _ _ hbij (bijective_appTop_of_isIso _))

theorem core {E B : Scheme.{u}} (p : E ⟶ B) (e : B ⟶ E) (he : e ≫ p = 𝟙 B)
    (φ : pullback p p ⟶ E) (hφ : φ ≫ p = pullback.fst p p ≫ p)
    (w₁ : 𝟙 E ≫ p = (p ≫ e) ≫ p) (hconst : pullback.lift (𝟙 E) (p ≫ e) w₁ ≫ φ = p ≫ e)
    (w₂ : (p ≫ e) ≫ p = 𝟙 E ≫ p)
    (k : Type u) [Field k] (bk : Spec (CommRingCat.of k) ⟶ B)
    [IsProper (pullback.snd p bk)] [IsIntegral ↑(pullback p bk)]
    (ξ : Spec (CommRingCat.of k) ⟶ pullback p p) (hξb : ξ ≫ pullback.snd p p ≫ p = bk) :
    ξ ≫ φ = ξ ≫ pullback.snd p p ≫ pullback.lift (p ≫ e) (𝟙 E) w₂ ≫ φ := by
  have hconn : ConnectedSpace ↑(pullback p bk) := inferInstance

  have wek : (bk ≫ e) ≫ p = 𝟙 _ ≫ bk := by rw [Category.assoc, he, Category.comp_id, Category.id_comp]
  have hek : pullback.lift (bk ≫ e) (𝟙 _) wek ≫ pullback.snd p bk = 𝟙 _ := pullback.lift_snd _ _ _
  have hek1 : pullback.lift (bk ≫ e) (𝟙 _) wek ≫ pullback.fst p bk = bk ≫ e := pullback.lift_fst _ _ _

  have wm : (pullback.fst (pullback.snd p bk) (pullback.snd p bk) ≫ pullback.fst p bk) ≫ p =
      (pullback.snd (pullback.snd p bk) (pullback.snd p bk) ≫ pullback.fst p bk) ≫ p := by
    simp only [Category.assoc, pullback.condition]
    rw [pullback.condition_assoc]
  have hm1 := pullback.lift_fst _ _ wm
  have hm2 := pullback.lift_snd _ _ wm

  have wφ : (pullback.lift _ _ wm ≫ φ) ≫ p =
      (pullback.fst (pullback.snd p bk) (pullback.snd p bk) ≫ pullback.snd p bk) ≫ bk := by
    rw [Category.assoc, hφ, ← Category.assoc, hm1, Category.assoc, pullback.condition, Category.assoc]
  have hφk1 := pullback.lift_fst _ _ wφ
  have hφk := pullback.lift_snd _ _ wφ

  have wι₁ : 𝟙 (pullback p bk) ≫ pullback.snd p bk =
      (pullback.snd p bk ≫ pullback.lift (bk ≫ e) (𝟙 _) wek) ≫ pullback.snd p bk := by
    rw [Category.id_comp, Category.assoc, hek, Category.comp_id]
  have h1 : pullback.lift (𝟙 (pullback p bk)) (pullback.snd p bk ≫ pullback.lift (bk ≫ e) (𝟙 _) wek) wι₁ ≫
      pullback.lift _ _ wm = pullback.fst p bk ≫ pullback.lift (𝟙 E) (p ≫ e) w₁ := by
    apply pullback.hom_ext
    · simp only [Category.assoc, hm1, pullback.lift_fst_assoc, Category.id_comp, pullback.lift_fst,
        Category.comp_id]
    · simp only [Category.assoc, hm2, pullback.lift_snd_assoc, pullback.lift_snd, hek1]
      rw [pullback.condition_assoc]
  have hconstk : pullback.lift (𝟙 (pullback p bk)) (pullback.snd p bk ≫ pullback.lift (bk ≫ e) (𝟙 _) wek) wι₁ ≫
      pullback.lift _ _ wφ = pullback.snd p bk ≫ pullback.lift (bk ≫ e) (𝟙 _) wek := by
    apply pullback.hom_ext
    · rw [Category.assoc, hφk1, ← Category.assoc, h1, Category.assoc, hconst, pullback.condition_assoc,
        Category.assoc, hek1]
    · rw [Category.assoc, hφk, ← Category.assoc, pullback.lift_fst, Category.id_comp, Category.assoc, hek,
        Category.comp_id]

  have H := AlgebraicGeometry.exists_eq_snd_comp_of_comp_eq_const_of_isProper k
    (pullback.snd p bk) (pullback.snd p bk) hconn (pullback.snd p bk)
    (pullback.lift (bk ≫ e) (𝟙 _) wek) hek (pullback.lift (bk ≫ e) (𝟙 _) wek) hek
    (pullback.lift _ _ wφ) hφk (pullback.lift (bk ≫ e) (𝟙 _) wek) hconstk

  have hξ1 : (ξ ≫ pullback.fst p p) ≫ p = 𝟙 _ ≫ bk := by
    rw [Category.id_comp, ← hξb, Category.assoc, pullback.condition]
  have hξ2 : (ξ ≫ pullback.snd p p) ≫ p = 𝟙 _ ≫ bk := by rw [Category.id_comp, ← hξb, Category.assoc]
  have wξ : pullback.lift (ξ ≫ pullback.fst p p) (𝟙 _) hξ1 ≫ pullback.snd p bk =
      pullback.lift (ξ ≫ pullback.snd p p) (𝟙 _) hξ2 ≫ pullback.snd p bk := by
    rw [pullback.lift_snd, pullback.lift_snd]
  have hξm : pullback.lift _ _ wξ ≫ pullback.lift _ _ wm = ξ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hm1, ← Category.assoc, pullback.lift_fst, pullback.lift_fst]
    · rw [Category.assoc, hm2, ← Category.assoc, pullback.lift_snd, pullback.lift_fst]
  have wι₂ : (pullback.snd p bk ≫ pullback.lift (bk ≫ e) (𝟙 _) wek) ≫ pullback.snd p bk =
      𝟙 (pullback p bk) ≫ pullback.snd p bk := by
    rw [Category.assoc, hek, Category.comp_id, Category.id_comp]
  have hlift : pullback.lift (pullback.snd p bk ≫ pullback.lift (bk ≫ e) (𝟙 _) wek) (𝟙 (pullback p bk)) wι₂ ≫
      pullback.lift _ _ wm = pullback.fst p bk ≫ pullback.lift (p ≫ e) (𝟙 E) w₂ := by
    apply pullback.hom_ext
    · simp only [Category.assoc, hm1, pullback.lift_fst_assoc, pullback.lift_fst, hek1]
      rw [pullback.condition_assoc]
    · simp only [Category.assoc, hm2, pullback.lift_snd_assoc, Category.id_comp, pullback.lift_snd,
        Category.comp_id]

  have hH := congrArg (fun g => pullback.lift _ _ wξ ≫ g ≫ pullback.fst p bk) H
  simp only [Category.assoc, hφk1] at hH
  rw [← Category.assoc (pullback.lift _ _ wξ) (pullback.lift _ _ wm), hξm] at hH
  rw [hH, ← Category.assoc (pullback.lift _ _ wι₂) (pullback.lift _ _ wm) φ, hlift]
  simp only [Category.assoc]
  rw [← Category.assoc (pullback.lift _ _ wξ), pullback.lift_snd,
    ← Category.assoc (pullback.lift (ξ ≫ pullback.snd p p) (𝟙 _) hξ2), pullback.lift_fst, Category.assoc]

theorem base_eq_of_comp_eq_const {R : Type u} [CommRing R] (V : WeierstrassCurve.Projective R) [V.toAffine.IsElliptic]
    (e : Spec (CommRingCat.of R) ⟶ projModelCR V) (he : e ≫ projModelStrCR V = 𝟙 _)
    (φ : pullback (projModelStrCR V) (projModelStrCR V) ⟶ projModelCR V)
    (hφ : φ ≫ projModelStrCR V = pullback.fst (projModelStrCR V) (projModelStrCR V) ≫ projModelStrCR V)
    (w₁ : 𝟙 (projModelCR V) ≫ projModelStrCR V = (projModelStrCR V ≫ e) ≫ projModelStrCR V)
    (hconst : pullback.lift (𝟙 (projModelCR V)) (projModelStrCR V ≫ e) w₁ ≫ φ = projModelStrCR V ≫ e)
    (w₂ : (projModelStrCR V ≫ e) ≫ projModelStrCR V = 𝟙 (projModelCR V) ≫ projModelStrCR V)
    (x : ↑(pullback (projModelStrCR V) (projModelStrCR V))) :
    φ.base x = φ.base ((pullback.lift (projModelStrCR V ≫ e) (𝟙 (projModelCR V)) w₂).base
        ((pullback.snd (projModelStrCR V) (projModelStrCR V)).base x)) := by

  let κ : Type u := ↑((pullback (projModelStrCR V) (projModelStrCR V)).residueField x)
  let k : Type u := AlgebraicClosure κ
  let ξ : Spec (CommRingCat.of k) ⟶ pullback (projModelStrCR V) (projModelStrCR V) :=
    Spec.map (CommRingCat.ofHom (algebraMap κ k)) ≫
      (pullback (projModelStrCR V) (projModelStrCR V)).fromSpecResidueField x
  have hξ : ∀ q : ↑(Spec (CommRingCat.of k)), ξ.base q = x := by
    intro q
    have : ξ.base q ∈ Set.range ((pullback (projModelStrCR V) (projModelStrCR V)).fromSpecResidueField x).base := by
      simp only [ξ, Scheme.Hom.comp_base, TopCat.comp_app]
      exact ⟨_, rfl⟩
    rwa [Scheme.range_fromSpecResidueField, Set.mem_singleton_iff] at this

  let b : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R) :=
    ξ ≫ pullback.snd (projModelStrCR V) (projModelStrCR V) ≫ projModelStrCR V
  letI : Algebra R k := (Spec.preimage b).hom.toAlgebra
  have hbk : Spec.map (CommRingCat.ofHom (algebraMap R k)) = b := by
    rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom, Spec.map_preimage]
  obtain ⟨hprop, hint, -⟩ :=
    WeierstrassProjModel.isProper_and_isIntegral_and_isReduced_selfPullback_pullback_snd_of_baseChangeIso V k
      (WeierstrassProjModel.projModel_pullback_iso_baseChange V k)
  haveI := hprop
  haveI := hint
  have key := core (projModelStrCR V) e he φ hφ w₁ hconst w₂ k
    (Spec.map (CommRingCat.ofHom (algebraMap R k))) ξ (by rw [hbk])
  let q : ↑(Spec (CommRingCat.of k)) := ⟨⊥, Ideal.isPrime_bot⟩
  have hq := congrArg (fun g => g.base q) key
  simp only [Scheme.Hom.comp_base, TopCat.comp_app] at hq
  rwa [hξ q] at hq

end K1cAux

theorem solution
    {R : Type u} [CommRing R] (V : WeierstrassCurve.Projective R) [V.toAffine.IsElliptic]
    (e : Spec (CommRingCat.of R) ⟶ projModelCR V) (he : e ≫ projModelStrCR V = 𝟙 _)
    (φ : pullback (projModelStrCR V) (projModelStrCR V) ⟶ projModelCR V)
    (hφ : φ ≫ projModelStrCR V = pullback.fst (projModelStrCR V) (projModelStrCR V) ≫ projModelStrCR V)
    (hconst : pullback.lift (𝟙 (projModelCR V)) (projModelStrCR V ≫ e)
        (by rw [Category.id_comp, Category.assoc, he, Category.comp_id]) ≫ φ = projModelStrCR V ≫ e) :
    φ = pullback.snd (projModelStrCR V) (projModelStrCR V) ≫
      (pullback.lift (projModelStrCR V ≫ e) (𝟙 (projModelCR V))
        (by rw [Category.assoc, he, Category.comp_id, Category.id_comp]) ≫ φ) := by
  haveI : IsProper (projModelStrCR V) := WeierstrassProjModel.projModelStrCR_isProper V
  have hsec : pullback.lift (projModelStrCR V ≫ e) (𝟙 (projModelCR V))
      (by rw [Category.assoc, he, Category.comp_id, Category.id_comp]) ≫
      pullback.snd (projModelStrCR V) (projModelStrCR V) = 𝟙 _ := pullback.lift_snd _ _ _
  have hclosed : IsClosedMap (pullback.snd (projModelStrCR V) (projModelStrCR V)).base :=
    (pullback.snd (projModelStrCR V) (projModelStrCR V)).isClosedMap
  have hΓ : ∀ U : (projModelCR V).Opens, IsAffineOpen U →
      Function.Bijective ((pullback.snd (projModelStrCR V) (projModelStrCR V)) ∣_ U).appTop :=
    K1cAux.bijective_appTop_snd_restrict_of (projModelStrCR V)
      (fun S _ _ => WeierstrassProjModel.bijective_appTop_pullback_snd_projModelStrCR V S)
  have hfib := K1cAux.base_eq_of_comp_eq_const V e he φ hφ _ hconst
    (by rw [Category.assoc, he, Category.comp_id, Category.id_comp])
  have H := K1cAux.eq_comp_of_isClosedMap_of_bijective_app
    (pullback.snd (projModelStrCR V) (projModelStrCR V)) _ hsec hclosed hΓ φ hfib
  simpa only [Category.assoc] using H

end S_WeierstrassProjModel_eq_snd_comp_of_comp_eq_const_of_isElliptic
end P2MW
export P2MW.S_WeierstrassProjModel_eq_snd_comp_of_comp_eq_const_of_isElliptic (solution)
