-- Prove2me | solution 1 for WeierstrassProjModel.projModelCR_sections_twoChart
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/25a02968-8731-5fa8-b129-7dd1da1b1ee6

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_projModelCR_sections_twoChart

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel HomogeneousLocalization HomogeneousIdealQuotientGrading

attribute [local instance] MvPolynomial.gradedAlgebra

namespace K1bAlphaAux

open MvPolynomial TopologicalSpace

section Cover

variable {R : Type u} [CommRing R] (V : WeierstrassCurve.Projective R)

theorem polynomial_add_X0_cube :
    V.polynomial + X 0 ^ 3 = X 2 * (X 1 ^ 2 + C V.a₁ * X 0 * X 1 + C V.a₃ * X 1 * X 2
      - C V.a₂ * X 0 ^ 2 - C V.a₄ * X 0 * X 2 - C V.a₆ * X 2 ^ 2) := by
  rw [WeierstrassCurve.Projective.polynomial]
  ring

theorem not_mem_and_mem (x : Proj (projModelGradingCR V)) :
    ¬ (Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal (X 1 : MvPolynomial (Fin 3) R)
          ∈ x.asHomogeneousIdeal ∧
       Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal (X 2 : MvPolynomial (Fin 3) R)
          ∈ x.asHomogeneousIdeal) := by
  rintro ⟨h1, h2⟩
  have hpoly : Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal V.polynomial = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  have hid := congrArg (Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal) (polynomial_add_X0_cube V)
  rw [map_add, map_mul, map_pow, hpoly, zero_add] at hid
  have h0 : Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal (X 0 : MvPolynomial (Fin 3) R)
      ∈ x.asHomogeneousIdeal.toIdeal := by
    apply x.isPrime.mem_of_pow_mem 3
    rw [hid]
    exact Ideal.mul_mem_right _ _ h2
  have hspan : Ideal.span (Set.range fun i : Fin 3 ↦
      Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal (X i : MvPolynomial (Fin 3) R))
        ≤ x.asHomogeneousIdeal.toIdeal := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  exact x.not_irrelevant_le fun z hz ↦ hspan (kw_pbac_irrelevant_le_span_mk_X_CR R V hz)

theorem top_le_sup :
    (⊤ : Opens (Proj (projModelGradingCR V))) ≤
      Proj.basicOpen (projModelGradingCR V)
          (Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal (X 1 : MvPolynomial (Fin 3) R)) ⊔
        Proj.basicOpen (projModelGradingCR V)
          (Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal (X 2 : MvPolynomial (Fin 3) R)) := by
  intro x _
  rw [Opens.mem_sup, Proj.mem_basicOpen, Proj.mem_basicOpen]
  by_cases h1 : Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal (X 1 : MvPolynomial (Fin 3) R)
      ∈ x.asHomogeneousIdeal
  · exact Or.inr fun h2 => not_mem_and_mem V x ⟨h1, h2⟩
  · exact Or.inl h1

end Cover

end K1bAlphaAux

namespace K1bAlphaAux

open TopologicalSpace

theorem map_homOfLE_comp {X : Scheme.{u}} (U V W : X.Opens) (h₁ : U ≤ V) (h₂ : V ≤ W) (h₃ : U ≤ W)
    (s : Γ(X, W)) :
    X.presheaf.map (homOfLE h₃).op s =
      X.presheaf.map (homOfLE h₁).op (X.presheaf.map (homOfLE h₂).op s) := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp]

theorem read_const {A : Type u} {σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] {m : ℕ} (hm : 0 < m) (k : A) (hk : k ∈ 𝒜 m) (r : 𝒜 0) :
    (Proj.basicOpenIsoAway 𝒜 k hk hm).inv
      ((Proj 𝒜).presheaf.map (homOfLE (le_top : Proj.basicOpen 𝒜 k ≤ ⊤)).op
        ((Proj.toSpecZero 𝒜).appTop ((Scheme.ΓSpecIso (CommRingCat.of (𝒜 0))).inv r))) =
    fromZeroRingHom 𝒜 (Submonoid.powers k) r := by

  have H0 := congrArg Scheme.Hom.appTop (Proj.awayι_toSpecZero 𝒜 k hk hm)
  rw [Scheme.Hom.comp_appTop, Proj.awayι, Scheme.Hom.comp_appTop] at H0
  have H1 := ConcreteCategory.congr_hom H0 ((Scheme.ΓSpecIso (CommRingCat.of (𝒜 0))).inv r)
  have H2 := ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (fromZeroRingHom 𝒜 (Submonoid.powers k)))) r
  rw [CommRingCat.comp_apply, CommRingCat.comp_apply] at H2
  rw [CommRingCat.comp_apply, CommRingCat.comp_apply, ← H2] at H1

  have hcancel : ∀ y, (Proj.basicOpenIsoSpec 𝒜 k hk hm).hom.appTop
      ((Proj.basicOpenIsoSpec 𝒜 k hk hm).inv.appTop y) = y := by
    intro y
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, Iso.hom_inv_id, Scheme.Hom.id_appTop,
      CommRingCat.id_apply]
  have H3 := congrArg (Proj.basicOpenIsoSpec 𝒜 k hk hm).hom.appTop H1
  rw [hcancel] at H3
  rw [Proj.basicOpenIsoSpec_hom,
    show (Proj.basicOpenToSpec 𝒜 k).appTop = (Proj.basicOpenToSpec 𝒜 k).app ⊤ from rfl,
    Proj.basicOpenToSpec_app_top, CommRingCat.comp_apply, CommRingCat.comp_apply, Iso.inv_hom_id_apply] at H3

  have H4 := congrArg (Proj.basicOpen 𝒜 k).topIso.hom H3
  rw [Iso.inv_hom_id_apply] at H4
  have H5 : ∀ t, (Proj.basicOpen 𝒜 k).topIso.hom ((Proj.basicOpen 𝒜 k).ι.appTop t) =
      (Proj 𝒜).presheaf.map (homOfLE (le_top : Proj.basicOpen 𝒜 k ≤ ⊤)).op t := by
    intro t
    rw [Scheme.Opens.topIso_hom, Scheme.Opens.ι_appTop]
    erw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rw [H5] at H4
  rw [H4, ← Proj.basicOpenIsoAway_hom 𝒜 k hk hm, Iso.hom_inv_id_apply]
  rfl

theorem twoChart {A : Type u} {σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] {m : ℕ} (hm : 0 < m) (f g : A) (hf : f ∈ 𝒜 m) (hg : g ∈ 𝒜 m)
    (hcov : (⊤ : (Proj 𝒜).Opens) ≤ Proj.basicOpen 𝒜 f ⊔ Proj.basicOpen 𝒜 g) :
    let ρf : Γ(Proj 𝒜, ⊤) ⟶ CommRingCat.of (Away 𝒜 f) :=
      (Proj 𝒜).presheaf.map (homOfLE le_top).op ≫ (Proj.basicOpenIsoAway 𝒜 f hf hm).inv
    let ρg : Γ(Proj 𝒜, ⊤) ⟶ CommRingCat.of (Away 𝒜 g) :=
      (Proj 𝒜).presheaf.map (homOfLE le_top).op ≫ (Proj.basicOpenIsoAway 𝒜 g hg hm).inv
    (∀ s t : Γ(Proj 𝒜, ⊤), ρf s = ρf t → ρg s = ρg t → s = t) ∧
    (∀ (a : Away 𝒜 f) (b : Away 𝒜 g),
      awayMap 𝒜 hg (rfl : f * g = f * g) a = awayMap 𝒜 hf (mul_comm f g) b →
      ∃ s : Γ(Proj 𝒜, ⊤), ρf s = a ∧ ρg s = b) ∧
    (∀ s : Γ(Proj 𝒜, ⊤), awayMap 𝒜 hg (rfl : f * g = f * g) (ρf s) = awayMap 𝒜 hf (mul_comm f g) (ρg s)) ∧
    (∀ r : 𝒜 0,
      ρf ((Proj.toSpecZero 𝒜).appTop ((Scheme.ΓSpecIso (CommRingCat.of (𝒜 0))).inv r)) =
        fromZeroRingHom 𝒜 (Submonoid.powers f) r ∧
      ρg ((Proj.toSpecZero 𝒜).appTop ((Scheme.ΓSpecIso (CommRingCat.of (𝒜 0))).inv r)) =
        fromZeroRingHom 𝒜 (Submonoid.powers g) r) := by
  intro ρf ρg
  classical
  have hfg : f * g ∈ 𝒜 (m + m) := SetLike.mul_mem_graded hf hg
  have h2 : 0 < m + m := Nat.add_pos_left hm m
  have hle₁ : Proj.basicOpen 𝒜 (f * g) ≤ Proj.basicOpen 𝒜 f := Proj.basicOpen_mono _ _ _ ⟨_, rfl⟩
  have hle₂ : Proj.basicOpen 𝒜 (f * g) ≤ Proj.basicOpen 𝒜 g := Proj.basicOpen_mono _ _ _ ⟨_, mul_comm f g⟩
  have h12 : Proj.basicOpen 𝒜 (f * g) = Proj.basicOpen 𝒜 f ⊓ Proj.basicOpen 𝒜 g := Proj.basicOpen_mul _ _ _

  have keyf : ∀ a : Away 𝒜 f,
      (Proj 𝒜).presheaf.map (homOfLE hle₁).op ((Proj.basicOpenIsoAway 𝒜 f hf hm).hom a) =
        (Proj.basicOpenIsoAway 𝒜 (f * g) hfg h2).hom (awayMap 𝒜 hg (rfl : f * g = f * g) a) := by
    intro a
    have := ConcreteCategory.congr_hom (Proj.awayMap_awayToSection 𝒜 hg (rfl : f * g = f * g)) a
    rw [Proj.basicOpenIsoAway_hom, Proj.basicOpenIsoAway_hom]
    rw [CommRingCat.comp_apply, CommRingCat.comp_apply] at this
    exact this.symm
  have keyg : ∀ b : Away 𝒜 g,
      (Proj 𝒜).presheaf.map (homOfLE hle₂).op ((Proj.basicOpenIsoAway 𝒜 g hg hm).hom b) =
        (Proj.basicOpenIsoAway 𝒜 (f * g) hfg h2).hom (awayMap 𝒜 hf (mul_comm f g) b) := by
    intro b
    have := ConcreteCategory.congr_hom (Proj.awayMap_awayToSection 𝒜 hf (mul_comm f g)) b
    rw [Proj.basicOpenIsoAway_hom, Proj.basicOpenIsoAway_hom]
    rw [CommRingCat.comp_apply, CommRingCat.comp_apply] at this
    exact this.symm
  have hρf : ∀ s, ρf s = (Proj.basicOpenIsoAway 𝒜 f hf hm).inv
      ((Proj 𝒜).presheaf.map (homOfLE (le_top : Proj.basicOpen 𝒜 f ≤ ⊤)).op s) := fun s => rfl
  have hρg : ∀ s, ρg s = (Proj.basicOpenIsoAway 𝒜 g hg hm).inv
      ((Proj 𝒜).presheaf.map (homOfLE (le_top : Proj.basicOpen 𝒜 g ≤ ⊤)).op s) := fun s => rfl
  have hiii : ∀ s : Γ(Proj 𝒜, ⊤),
      awayMap 𝒜 hg (rfl : f * g = f * g) (ρf s) = awayMap 𝒜 hf (mul_comm f g) (ρg s) := by
    intro s
    apply (ConcreteCategory.bijective_of_isIso (Proj.basicOpenIsoAway 𝒜 (f * g) hfg h2).hom).1
    rw [← keyf, ← keyg, hρf, hρg, Iso.inv_hom_id_apply, Iso.inv_hom_id_apply,
      ← map_homOfLE_comp _ _ _ hle₁ le_top le_top, ← map_homOfLE_comp _ _ _ hle₂ le_top le_top]
  refine ⟨?_, ?_, hiii, ?_⟩
  ·
    intro s t hsf hsg
    rw [hρf, hρf] at hsf
    rw [hρg, hρg] at hsg
    have hsf' := congrArg (Proj.basicOpenIsoAway 𝒜 f hf hm).hom hsf
    have hsg' := congrArg (Proj.basicOpenIsoAway 𝒜 g hg hm).hom hsg
    simp only [Iso.inv_hom_id_apply] at hsf' hsg'
    exact (Proj 𝒜).sheaf.eq_of_locally_eq₂ (homOfLE (le_top : Proj.basicOpen 𝒜 f ≤ ⊤))
      (homOfLE (le_top : Proj.basicOpen 𝒜 g ≤ ⊤)) hcov s t hsf' hsg'
  ·
    intro a b hab
    have hcompat : (Proj 𝒜).presheaf.map
          (homOfLE (inf_le_left : Proj.basicOpen 𝒜 f ⊓ Proj.basicOpen 𝒜 g ≤ _)).op
          ((Proj.basicOpenIsoAway 𝒜 f hf hm).hom a) =
        (Proj 𝒜).presheaf.map
          (homOfLE (inf_le_right : Proj.basicOpen 𝒜 f ⊓ Proj.basicOpen 𝒜 g ≤ _)).op
          ((Proj.basicOpenIsoAway 𝒜 g hg hm).hom b) := by
      rw [map_homOfLE_comp _ (Proj.basicOpen 𝒜 (f * g)) _ h12.ge hle₁ inf_le_left,
        map_homOfLE_comp _ (Proj.basicOpen 𝒜 (f * g)) _ h12.ge hle₂ inf_le_right, keyf, keyg, hab]
    obtain ⟨s', hs'1, hs'2⟩ : ∃ s' : Γ(Proj 𝒜, Proj.basicOpen 𝒜 f ⊔ Proj.basicOpen 𝒜 g),
        (Proj 𝒜).presheaf.map (homOfLE le_sup_left).op s' = (Proj.basicOpenIsoAway 𝒜 f hf hm).hom a ∧
        (Proj 𝒜).presheaf.map (homOfLE le_sup_right).op s' = (Proj.basicOpenIsoAway 𝒜 g hg hm).hom b :=
      ⟨((Proj 𝒜).sheaf.objSupIsoProdEqLocus (Proj.basicOpen 𝒜 f) (Proj.basicOpen 𝒜 g)).inv ⟨(_, _), hcompat⟩,
        TopCat.Sheaf.objSupIsoProdEqLocus_inv_fst _ _ _ _,
        TopCat.Sheaf.objSupIsoProdEqLocus_inv_snd _ _ _ _⟩
    refine ⟨(Proj 𝒜).presheaf.map (homOfLE hcov).op s', ?_, ?_⟩
    · rw [hρf, ← map_homOfLE_comp _ _ _ le_top hcov le_sup_left s', hs'1]
      exact (Proj.basicOpenIsoAway 𝒜 f hf hm).hom_inv_id_apply a
    · rw [hρg, ← map_homOfLE_comp _ _ _ le_top hcov le_sup_right s', hs'2]
      exact (Proj.basicOpenIsoAway 𝒜 g hg hm).hom_inv_id_apply b
  ·
    intro r
    exact ⟨read_const 𝒜 hm f hf r, read_const 𝒜 hm g hg r⟩

end K1bAlphaAux

theorem solution
    {R : Type u} [CommRing R] (V : WeierstrassCurve.Projective R) :
    let 𝒜 := projModelGradingCR V
    let Y : ProjModelRingCR V := Ideal.Quotient.mk _ (MvPolynomial.X 1)
    let Z : ProjModelRingCR V := Ideal.Quotient.mk _ (MvPolynomial.X 2)
    let hY : Y ∈ 𝒜 1 :=
      mk_mem_quotGradingSubmodule _ _ ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_X R 1))
    let hZ : Z ∈ 𝒜 1 :=
      mk_mem_quotGradingSubmodule _ _ ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_X R 2))
    let ρY : Γ(Proj 𝒜, ⊤) ⟶ CommRingCat.of (Away 𝒜 Y) :=
      (Proj 𝒜).presheaf.map (homOfLE le_top).op ≫ (Proj.basicOpenIsoAway 𝒜 Y hY one_pos).inv
    let ρZ : Γ(Proj 𝒜, ⊤) ⟶ CommRingCat.of (Away 𝒜 Z) :=
      (Proj 𝒜).presheaf.map (homOfLE le_top).op ≫ (Proj.basicOpenIsoAway 𝒜 Z hZ one_pos).inv
    (∀ s t : Γ(Proj 𝒜, ⊤), ρY s = ρY t → ρZ s = ρZ t → s = t) ∧
    (∀ (a : Away 𝒜 Y) (b : Away 𝒜 Z),
      awayMap 𝒜 hZ (rfl : Y * Z = Y * Z) a = awayMap 𝒜 hY (mul_comm Y Z) b →
      ∃ s : Γ(Proj 𝒜, ⊤), ρY s = a ∧ ρZ s = b) ∧
    (∀ s : Γ(Proj 𝒜, ⊤), awayMap 𝒜 hZ (rfl : Y * Z = Y * Z) (ρY s) = awayMap 𝒜 hY (mul_comm Y Z) (ρZ s)) ∧
    (∀ r : 𝒜 0,
      ρY ((Proj.toSpecZero 𝒜).appTop ((Scheme.ΓSpecIso (CommRingCat.of (𝒜 0))).inv r)) =
        fromZeroRingHom 𝒜 (Submonoid.powers Y) r ∧
      ρZ ((Proj.toSpecZero 𝒜).appTop ((Scheme.ΓSpecIso (CommRingCat.of (𝒜 0))).inv r)) =
        fromZeroRingHom 𝒜 (Submonoid.powers Z) r) := by
  intro 𝒜 Y Z hY hZ ρY ρZ
  exact K1bAlphaAux.twoChart 𝒜 one_pos Y Z hY hZ (K1bAlphaAux.top_le_sup V)

end S_WeierstrassProjModel_projModelCR_sections_twoChart
end P2MW
export P2MW.S_WeierstrassProjModel_projModelCR_sections_twoChart (solution)
