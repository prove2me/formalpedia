-- Prove2me | solution 1 for WeierstrassProjModel.exists_ne_forall_exists_eq_specMap_map_smul_comp_of_specMap_fstHom_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/63f9ed90-d8b4-5b9c-b61d-394d4fa5f6fc

import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Theorems.Thm_WeierstrassProjModel_exists_isCoefficientHom
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isPullback_projMap_of_isCoefficientHom
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_zChartIota_comp_projMap_eq_specMap_comp_zChartIota
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_equation_iff_exists_isSectionThrough_and_eq_iff_of_isSectionThrough
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_isSectionThrough_of_specMap_comp_eq_zChart
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_isSectionThrough_or_exists_reducesToOrigin
import Theorems.Thm_WeierstrassCurve_Affine_exists_ne_zero_forall_equation_dualNumber_iff
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_section_reducesToOrigin_originParam_eq
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_section_eq_of_reducesToOrigin_of_originParam_eq
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_reducesToOrigin_of_specMap_comp_eq_originChart
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_exists_ne_forall_exists_eq_specMap_map_smul_comp_of_specMap_fstHom_comp_eq
p2m_attr_erase "instance" "WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType"
p2m_attr_erase "simp" "WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X"

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal IsLocalRing FormalGroup
attribute [local instance] MvPolynomial.gradedAlgebra

open HomogeneousLocalization TrivSqZeroExt DualNumber

namespace LiftsLineAux

section Dual

theorem mem_maximalIdeal_field_iff {k : Type} [Field k] (a : k) : a ∈ maximalIdeal k ↔ a = 0 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_ne_zero, not_not]

theorem mem_maximalIdeal_dualNumber_iff {k : Type} [Field k] (z : DualNumber k) :
    z ∈ maximalIdeal (DualNumber k) ↔ z.fst = 0 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, TrivSqZeroExt.isUnit_iff_isUnit_fst, isUnit_iff_ne_zero,
    not_not]

theorem eps_mem_maximalIdeal (k : Type) [Field k] : (ε : DualNumber k) ∈ maximalIdeal (DualNumber k) := by
  rw [mem_maximalIdeal_dualNumber_iff, fst_eps]

theorem eps_ne_zero (k : Type) [Field k] : (ε : DualNumber k) ≠ 0 := by
  intro h
  have := congrArg TrivSqZeroExt.snd h
  rw [snd_eps, TrivSqZeroExt.snd_zero] at this
  exact one_ne_zero this

theorem maximalIdeal_dualNumber_sq (k : Type) [Field k] : maximalIdeal (DualNumber k) ^ 2 = ⊥ := by
  rw [DualNumber.maximalIdeal_eq_span_singleton_eps, Ideal.span_singleton_pow, eps_pow_two, Ideal.span_singleton_eq_bot]

theorem isAdicComplete_dualNumber (k : Type) [Field k] : IsAdicComplete (maximalIdeal (DualNumber k)) (DualNumber k) where
  haus' x hx := by
    have h2 := hx 2
    rw [SModEq.zero, maximalIdeal_dualNumber_sq, Submodule.bot_smul, Submodule.mem_bot] at h2
    exact h2
  prec' f hf := by
    refine ⟨f 2, fun m => ?_⟩
    by_cases h : m ≤ 2
    · exact hf h
    · have h2 := hf (show 2 ≤ m by omega)
      rw [maximalIdeal_dualNumber_sq, Submodule.bot_smul, SModEq.bot] at h2
      rw [h2]
      exact SModEq.rfl

theorem isAdicComplete_field (k : Type) [Field k] : IsAdicComplete (maximalIdeal k) k := inferInstance

theorem ker_fstHom_eq_maximalIdeal (k : Type) [Field k] :
    RingHom.ker (TrivSqZeroExt.fstHom k k k).toRingHom = maximalIdeal (DualNumber k) := by
  ext z
  rw [RingHom.mem_ker, mem_maximalIdeal_dualNumber_iff]
  rfl

theorem fstHom_apply' {k : Type} [Field k] (z : DualNumber k) : (TrivSqZeroExt.fstHom k k k).toRingHom z = z.fst := rfl

theorem fstHom_comp_algebraMap (k : Type) [Field k] :
    (TrivSqZeroExt.fstHom k k k).toRingHom.comp (algebraMap k (DualNumber k)) = RingHom.id k :=
  RingHom.ext fun a => by simp

theorem fstHom_eps (k : Type) [Field k] : (TrivSqZeroExt.fstHom k k k).toRingHom (ε : DualNumber k) = 0 := fst_eps

theorem mapSmul_comp_algebraMap (k : Type) [Field k] (c : k) :
    (TrivSqZeroExt.map (c • (LinearMap.id : k →ₗ[k] k))).toRingHom.comp (algebraMap k (DualNumber k)) =
      algebraMap k (DualNumber k) :=
  RingHom.ext fun a => (TrivSqZeroExt.map _).commutes a

@[scoped simp] theorem mapSmul_fst {k : Type} [Field k] (c : k) (z : DualNumber k) :
    ((TrivSqZeroExt.map (c • (LinearMap.id : k →ₗ[k] k))).toRingHom z).fst = z.fst := by
  simp

@[scoped simp] theorem mapSmul_snd {k : Type} [Field k] (c : k) (z : DualNumber k) :
    ((TrivSqZeroExt.map (c • (LinearMap.id : k →ₗ[k] k))).toRingHom z).snd = c * z.snd := by
  simp

theorem mapSmul_apply {k : Type} [Field k] (c : k) (z : DualNumber k) :
    (TrivSqZeroExt.map (c • (LinearMap.id : k →ₗ[k] k))).toRingHom z =
      TrivSqZeroExt.inl z.fst + TrivSqZeroExt.inr (c * z.snd) := by
  ext <;> simp

theorem mapSmul_eps {k : Type} [Field k] (c : k) :
    (TrivSqZeroExt.map (c • (LinearMap.id : k →ₗ[k] k))).toRingHom (ε : DualNumber k) = c • (ε : DualNumber k) := by
  ext <;> simp

theorem fstHom_comp_mapSmul (k : Type) [Field k] (c : k) :
    (TrivSqZeroExt.fstHom k k k).toRingHom.comp (TrivSqZeroExt.map (c • (LinearMap.id : k →ₗ[k] k))).toRingHom =
      (TrivSqZeroExt.fstHom k k k).toRingHom :=
  RingHom.ext fun z => by simp

theorem algebraMap_dualNumber_snd {k : Type} [Field k] (a : k) : (algebraMap k (DualNumber k) a).snd = 0 := by
  simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem algebraMap_dualNumber_fst {k : Type} [Field k] (a : k) : (algebraMap k (DualNumber k) a).fst = a := by
  simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem specMap_fstHom_comp_specMap_algebraMap (k : Type) [Field k] :
    Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) = 𝟙 _ := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, fstHom_comp_algebraMap, CommRingCat.ofHom_id, Spec.map_id]

theorem specMap_mapSmul_comp_specMap_algebraMap (k : Type) [Field k] (c : k) :
    Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map (c • (LinearMap.id : k →ₗ[k] k))).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) =
      Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, mapSmul_comp_algebraMap]

end Dual

section Charts

variable {T : Type} [CommRing T]

theorem eq_of_specMap_comp_zChartι_eq (W : WeierstrassCurve.Projective T) {T' : Type} [CommRing T']
    (ρ ρ' : ZChartRing W →+* T')
    (h : Spec.map (CommRingCat.ofHom ρ) ≫ zChartι W = Spec.map (CommRingCat.ofHom ρ') ≫ zChartι W) :
    ρ = ρ' := by
  have e := congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono (zChartι W)).mp h))
  simpa only [CommRingCat.hom_ofHom] using e

theorem eq_of_specMap_comp_originChartι_eq (W : WeierstrassCurve.Projective T) {T' : Type} [CommRing T']
    (χ χ' : OriginChartRing W →+* T')
    (h : Spec.map (CommRingCat.ofHom χ) ≫ originChartι W = Spec.map (CommRingCat.ofHom χ') ≫ originChartι W) :
    χ = χ' := by
  have e := congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono (originChartι W)).mp h))
  simpa only [CommRingCat.hom_ofHom] using e

theorem exists_originChartι_comp_projMap
    {T' : Type} [CommRing T'] (W : WeierstrassCurve.Projective T) (f : T →+* T')
    (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f))
    (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f)) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ)
    (hcoef : IsCoefficientHom W f φ) :
    ∃ a : OriginChartRing W →+* OriginChartRing (W.map f),
      originChartι (W.map f) ≫ Proj.map φ hφ = Spec.map (CommRingCat.ofHom a) ≫ originChartι W ∧
      a (xOverY W) = xOverY (W.map f) ∧ a (zOverY W) = zOverY (W.map f) := by
  obtain ⟨-, hX⟩ := hcoef
  have key : ∀ (s : ProjModelRingCR (W.map f)) (hs : s ∈ projModelGradingCR (W.map f) 1)
      (e : φ (coord W 1) = s),
      ∃ a : OriginChartRing W →+* Away (projModelGradingCR (W.map f)) s,
        Proj.awayι (projModelGradingCR (W.map f)) s hs one_pos ≫ Proj.map φ hφ =
          Spec.map (CommRingCat.ofHom a) ≫ originChartι W ∧
        a (xOverY W) = Away.mk (projModelGradingCR (W.map f)) hs 1 (coord (W.map f) 0)
          (by simpa using coord_mem (W.map f) 0) ∧
        a (zOverY W) = Away.mk (projModelGradingCR (W.map f)) hs 1 (coord (W.map f) 2)
          (by simpa using coord_mem (W.map f) 2) := by
    intro s hs e
    subst e
    refine ⟨Away.map φ (coord W 1), ?_, ?_, ?_⟩
    · exact Proj.awayι_comp_map φ hφ one_pos (coord W 1) (coord_mem W 1)
    · show Away.map φ (coord W 1) (Away.mk _ (coord_mem W 1) 1 (coord W 0) _) = _
      rw [Away.map_mk]
      apply HomogeneousLocalization.val_injective
      simp only [Away.val_mk]
      congr 1
      · exact hX 0
    · show Away.map φ (coord W 1) (Away.mk _ (coord_mem W 1) 1 (coord W 2) _) = _
      rw [Away.map_mk]
      apply HomogeneousLocalization.val_injective
      simp only [Away.val_mk]
      congr 1
      · exact hX 2
  exact key (coord (W.map f) 1) (coord_mem (W.map f) 1) (hX 1)

theorem exists_eq_comp_zChartι_of_comp_projMap_eq
    {T' T'' : Type} [CommRing T'] [CommRing T''] (W : WeierstrassCurve.Projective T) (f : T →+* T')
    (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f))
    (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f)) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ)
    (hcoef : IsCoefficientHom W f φ)
    (a : ZChartRing W →+* ZChartRing (W.map f))
    (ha : zChartι (W.map f) ≫ Proj.map φ hφ = Spec.map (CommRingCat.ofHom a) ≫ zChartι W)
    (p : Spec (CommRingCat.of T'') ⟶ projModelCR (W.map f)) (χ : ZChartRing W →+* T'')
    (hp : p ≫ Proj.map φ hφ = Spec.map (CommRingCat.ofHom χ) ≫ zChartι W) :
    ∃ χ' : ZChartRing (W.map f) →+* T'',
      p = Spec.map (CommRingCat.ofHom χ') ≫ zChartι (W.map f) ∧ χ'.comp a = χ := by
  classical
  obtain ⟨-, hX⟩ := hcoef
  have hrange : Set.range p ⊆ Set.range (zChartι (W.map f)) := by
    rintro _ ⟨x, rfl⟩
    have hx : (Proj.map φ hφ) (p x) ∈ (zChartι W).opensRange := by
      rw [Scheme.Hom.mem_opensRange]
      refine ⟨Spec.map (CommRingCat.ofHom χ) x, ?_⟩
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hp]
    have hx' : p x ∈ (zChartι (W.map f)).opensRange := by
      have e1 : (zChartι W).opensRange = Proj.basicOpen (projModelGradingCR W) (coord W 2) :=
        Proj.opensRange_awayι _ _ _ _
      have e2 : (zChartι (W.map f)).opensRange =
          Proj.basicOpen (projModelGradingCR (W.map f)) (coord (W.map f) 2) :=
        Proj.opensRange_awayι _ _ _ _
      rw [e1] at hx
      have hc : φ (coord W 2) = coord (W.map f) 2 := hX 2
      rw [e2, ← hc, ← Proj.map_preimage_basicOpen φ hφ]
      exact hx
    rw [Scheme.Hom.mem_opensRange] at hx'
    exact hx'
  set l := IsOpenImmersion.lift (zChartι (W.map f)) p hrange with hl_def
  have hl : l ≫ zChartι (W.map f) = p := IsOpenImmersion.lift_fac _ _ _
  set χ' : ZChartRing (W.map f) →+* T'' := (Spec.preimage l).hom with hχ'
  have hSpecχ' : Spec.map (CommRingCat.ofHom χ') = l := by
    rw [hχ', CommRingCat.ofHom_hom, Spec.map_preimage]
  refine ⟨χ', ?_, ?_⟩
  · rw [hSpecχ', hl]
  · have e1 : Spec.map (CommRingCat.ofHom (χ'.comp a)) ≫ zChartι W =
        Spec.map (CommRingCat.ofHom χ) ≫ zChartι W := by
      rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, ← ha, ← Category.assoc, hSpecχ', hl, hp]
    exact eq_of_specMap_comp_zChartι_eq W _ _ e1

theorem exists_eq_comp_originChartι_of_comp_projMap_eq
    {T' T'' : Type} [CommRing T'] [CommRing T''] (W : WeierstrassCurve.Projective T) (f : T →+* T')
    (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f))
    (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f)) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ)
    (hcoef : IsCoefficientHom W f φ)
    (a : OriginChartRing W →+* OriginChartRing (W.map f))
    (ha : originChartι (W.map f) ≫ Proj.map φ hφ = Spec.map (CommRingCat.ofHom a) ≫ originChartι W)
    (p : Spec (CommRingCat.of T'') ⟶ projModelCR (W.map f)) (χ : OriginChartRing W →+* T'')
    (hp : p ≫ Proj.map φ hφ = Spec.map (CommRingCat.ofHom χ) ≫ originChartι W) :
    ∃ χ' : OriginChartRing (W.map f) →+* T'',
      p = Spec.map (CommRingCat.ofHom χ') ≫ originChartι (W.map f) ∧ χ'.comp a = χ := by
  classical
  obtain ⟨-, hX⟩ := hcoef
  have hrange : Set.range p ⊆ Set.range (originChartι (W.map f)) := by
    rintro _ ⟨x, rfl⟩
    have hx : (Proj.map φ hφ) (p x) ∈ (originChartι W).opensRange := by
      rw [Scheme.Hom.mem_opensRange]
      refine ⟨Spec.map (CommRingCat.ofHom χ) x, ?_⟩
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hp]
    have hx' : p x ∈ (originChartι (W.map f)).opensRange := by
      have e1 : (originChartι W).opensRange = Proj.basicOpen (projModelGradingCR W) (coord W 1) :=
        Proj.opensRange_awayι _ _ _ _
      have e2 : (originChartι (W.map f)).opensRange =
          Proj.basicOpen (projModelGradingCR (W.map f)) (coord (W.map f) 1) :=
        Proj.opensRange_awayι _ _ _ _
      rw [e1] at hx
      have hc : φ (coord W 1) = coord (W.map f) 1 := hX 1
      rw [e2, ← hc, ← Proj.map_preimage_basicOpen φ hφ]
      exact hx
    rw [Scheme.Hom.mem_opensRange] at hx'
    exact hx'
  set l := IsOpenImmersion.lift (originChartι (W.map f)) p hrange with hl_def
  have hl : l ≫ originChartι (W.map f) = p := IsOpenImmersion.lift_fac _ _ _
  set χ' : OriginChartRing (W.map f) →+* T'' := (Spec.preimage l).hom with hχ'
  have hSpecχ' : Spec.map (CommRingCat.ofHom χ') = l := by
    rw [hχ', CommRingCat.ofHom_hom, Spec.map_preimage]
  refine ⟨χ', ?_, ?_⟩
  · rw [hSpecχ', hl]
  · have e1 : Spec.map (CommRingCat.ofHom (χ'.comp a)) ≫ originChartι W =
        Spec.map (CommRingCat.ofHom χ) ≫ originChartι W := by
      rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, ← ha, ← Category.assoc, hSpecχ', hl, hp]
    exact eq_of_specMap_comp_originChartι_eq W _ _ e1

theorem exists_section_comp_projMap_eq
    {T' : Type} [CommRing T'] (W : WeierstrassCurve.Projective T) (g : T →+* T')
    (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map g))
    (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map g)) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ)
    (hcoef : IsCoefficientHom W g φ)
    (q : Spec (CommRingCat.of T') ⟶ projModelCR W)
    (hq : q ≫ projModelStrCR W = Spec.map (CommRingCat.ofHom g)) :
    ∃ S : Section (W.map g), S.1 ≫ Proj.map φ hφ = q := by
  have hpb := WeierstrassCurve.DrinfeldGlobal.isPullback_projMap_of_isCoefficientHom W g φ hφ hcoef
  have w : q ≫ projModelStrCR W = 𝟙 _ ≫ Spec.map (CommRingCat.ofHom g) := by
    rw [Category.id_comp]; exact hq
  exact ⟨⟨hpb.lift q (𝟙 _) w, hpb.lift_snd _ _ _⟩, hpb.lift_fst _ _ _⟩

theorem section_comp_projMap_comp_str
    {T' : Type} [CommRing T'] (W : WeierstrassCurve.Projective T) (g : T →+* T')
    (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map g))
    (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map g)) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ)
    (hcoef : IsCoefficientHom W g φ) (S : Section (W.map g)) :
    (S.1 ≫ Proj.map φ hφ) ≫ projModelStrCR W = Spec.map (CommRingCat.ofHom g) := by
  have hpb := WeierstrassCurve.DrinfeldGlobal.isPullback_projMap_of_isCoefficientHom W g φ hφ hcoef
  rw [Category.assoc, hpb.w, ← Category.assoc, S.2, Category.id_comp]

end Charts

section Finite

variable {T T' : Type} [CommRing T] [CommRing T']

theorem eq_of_zChart_coords_eq (W : WeierstrassCurve.Projective T) (g : T →+* T')
    (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map g))
    (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map g)) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ)
    (hcoef : IsCoefficientHom W g φ)
    (a : ZChartRing W →+* ZChartRing (W.map g))
    (ha : zChartι (W.map g) ≫ Proj.map φ hφ = Spec.map (CommRingCat.ofHom a) ≫ zChartι W)
    (hax : a (xOverZ W) = xOverZ (W.map g)) (hay : a (yOverZ W) = yOverZ (W.map g))
    (q q' : Spec (CommRingCat.of T') ⟶ projModelCR W)
    (hq : q ≫ projModelStrCR W = Spec.map (CommRingCat.ofHom g))
    (hq' : q' ≫ projModelStrCR W = Spec.map (CommRingCat.ofHom g))
    (ρ ρ' : ZChartRing W →+* T')
    (hρ : q = Spec.map (CommRingCat.ofHom ρ) ≫ zChartι W)
    (hρ' : q' = Spec.map (CommRingCat.ofHom ρ') ≫ zChartι W)
    (hx : ρ (xOverZ W) = ρ' (xOverZ W)) (hy : ρ (yOverZ W) = ρ' (yOverZ W)) :
    q = q' := by
  obtain ⟨S, hS⟩ := exists_section_comp_projMap_eq W g φ hφ hcoef q hq
  obtain ⟨S', hS'⟩ := exists_section_comp_projMap_eq W g φ hφ hcoef q' hq'
  obtain ⟨χ, hχ, hχa⟩ := exists_eq_comp_zChartι_of_comp_projMap_eq W g φ hφ hcoef a ha S.1 ρ (by rw [hS, hρ])
  obtain ⟨χ', hχ', hχ'a⟩ := exists_eq_comp_zChartι_of_comp_projMap_eq W g φ hφ hcoef a ha S'.1 ρ' (by rw [hS', hρ'])
  have hthr : IsSectionThrough S (ρ (xOverZ W)) (ρ (yOverZ W)) := by
    refine ⟨χ, hχ, ?_, ?_⟩
    · show χ (xOverZ (W.map g)) = ρ (xOverZ W)
      rw [← hax, ← hχa, RingHom.comp_apply]
    · show χ (yOverZ (W.map g)) = ρ (yOverZ W)
      rw [← hay, ← hχa, RingHom.comp_apply]
  have hthr' : IsSectionThrough S' (ρ (xOverZ W)) (ρ (yOverZ W)) := by
    refine ⟨χ', hχ', ?_, ?_⟩
    · show χ' (xOverZ (W.map g)) = ρ (xOverZ W)
      rw [hx, ← hax, ← hχ'a, RingHom.comp_apply]
    · show χ' (yOverZ (W.map g)) = ρ (yOverZ W)
      rw [hy, ← hay, ← hχ'a, RingHom.comp_apply]
  have hSS' : S = S' :=
    ((WeierstrassCurve.DrinfeldGlobal.equation_iff_exists_isSectionThrough_and_eq_iff_of_isSectionThrough
      (W.map g)).2 S S' _ _ _ _ hthr hthr').mpr ⟨rfl, rfl⟩
  rw [← hS, ← hS', hSS']

theorem exists_point_zChart (W : WeierstrassCurve.Projective T) (g : T →+* T')
    (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map g))
    (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map g)) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ)
    (hcoef : IsCoefficientHom W g φ)
    (a : ZChartRing W →+* ZChartRing (W.map g))
    (ha : zChartι (W.map g) ≫ Proj.map φ hφ = Spec.map (CommRingCat.ofHom a) ≫ zChartι W)
    (hax : a (xOverZ W) = xOverZ (W.map g)) (hay : a (yOverZ W) = yOverZ (W.map g))
    (x y : T') (hxy : (W.map g).toAffine.Equation x y) :
    ∃ q : Spec (CommRingCat.of T') ⟶ projModelCR W,
      q ≫ projModelStrCR W = Spec.map (CommRingCat.ofHom g) ∧
      ∃ ρ : ZChartRing W →+* T', q = Spec.map (CommRingCat.ofHom ρ) ≫ zChartι W ∧
        ρ (xOverZ W) = x ∧ ρ (yOverZ W) = y := by
  obtain ⟨S, χ, hχ, hχx, hχy⟩ :=
    ((WeierstrassCurve.DrinfeldGlobal.equation_iff_exists_isSectionThrough_and_eq_iff_of_isSectionThrough
      (W.map g)).1 x y).mp hxy
  have hχ' : S.1 = Spec.map (CommRingCat.ofHom χ) ≫ zChartι (W.map g) := hχ
  refine ⟨S.1 ≫ Proj.map φ hφ, section_comp_projMap_comp_str W g φ hφ hcoef S, χ.comp a, ?_, ?_, ?_⟩
  · rw [hχ', Category.assoc, ha, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  · show χ (a (xOverZ W)) = x
    rw [hax]; exact hχx
  · show χ (a (yOverZ W)) = y
    rw [hay]; exact hχy

theorem exists_zChart_of_reduction (W : WeierstrassCurve.Projective T) (g : T →+* T')
    (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map g))
    (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map g)) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ)
    (hcoef : IsCoefficientHom W g φ)
    (a : ZChartRing W →+* ZChartRing (W.map g))
    (ha : zChartι (W.map g) ≫ Proj.map φ hφ = Spec.map (CommRingCat.ofHom a) ≫ zChartι W)
    (hax : a (xOverZ W) = xOverZ (W.map g)) (hay : a (yOverZ W) = yOverZ (W.map g))
    [IsLocalRing T'] {K : Type} [Field K] (π : T' →+* K) (hπ : RingHom.ker π = maximalIdeal T')
    (q : Spec (CommRingCat.of T') ⟶ projModelCR W)
    (hq : q ≫ projModelStrCR W = Spec.map (CommRingCat.ofHom g))
    (ρ₀ : ZChartRing W →+* K)
    (h₀ : Spec.map (CommRingCat.ofHom π) ≫ q = Spec.map (CommRingCat.ofHom ρ₀) ≫ zChartι W) :
    ∃ ρ : ZChartRing W →+* T', q = Spec.map (CommRingCat.ofHom ρ) ≫ zChartι W ∧
      π (ρ (xOverZ W)) = ρ₀ (xOverZ W) ∧ π (ρ (yOverZ W)) = ρ₀ (yOverZ W) ∧
      (W.map g).toAffine.Equation (ρ (xOverZ W)) (ρ (yOverZ W)) := by
  obtain ⟨S, hS⟩ := exists_section_comp_projMap_eq W g φ hφ hcoef q hq
  obtain ⟨ρbar, hρbar, hρbara⟩ := exists_eq_comp_zChartι_of_comp_projMap_eq W g φ hφ hcoef a ha
    (Spec.map (CommRingCat.ofHom π) ≫ S.1) ρ₀ (by rw [Category.assoc, hS, h₀])
  obtain ⟨x, y, ⟨χ, hχ, hχx, hχy⟩, hπx, hπy⟩ :=
    WeierstrassCurve.DrinfeldGlobal.exists_isSectionThrough_of_specMap_comp_eq_zChart (W.map g) S π hπ ρbar hρbar
  have hχ' : S.1 = Spec.map (CommRingCat.ofHom χ) ≫ zChartι (W.map g) := hχ
  have ex : χ (xOverZ (W.map g)) = x := hχx
  have ey : χ (yOverZ (W.map g)) = y := hχy
  have hEq : (W.map g).toAffine.Equation x y :=
    ((WeierstrassCurve.DrinfeldGlobal.equation_iff_exists_isSectionThrough_and_eq_iff_of_isSectionThrough
      (W.map g)).1 x y).mpr ⟨S, χ, hχ, hχx, hχy⟩
  refine ⟨χ.comp a, ?_, ?_, ?_, ?_⟩
  · rw [← hS, hχ', Category.assoc, ha, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  · show π (χ (a (xOverZ W))) = ρ₀ (xOverZ W)
    rw [hax, ex, hπx, ← hax, ← hρbara, RingHom.comp_apply]
  · show π (χ (a (yOverZ W))) = ρ₀ (yOverZ W)
    rw [hay, ey, hπy, ← hay, ← hρbara, RingHom.comp_apply]
  · show (W.map g).toAffine.Equation (χ (a (xOverZ W))) (χ (a (yOverZ W)))
    rw [hax, hay, ex, ey]
    exact hEq

end Finite

section Origin

variable {T T' : Type} [CommRing T] [CommRing T']

theorem eq_of_originParam_eq (W : WeierstrassCurve.Projective T) (g : T →+* T')
    (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map g))
    (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map g)) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ)
    (hcoef : IsCoefficientHom W g φ)
    (a : OriginChartRing W →+* OriginChartRing (W.map g))
    (ha : originChartι (W.map g) ≫ Proj.map φ hφ = Spec.map (CommRingCat.ofHom a) ≫ originChartι W)
    (hax : a (xOverY W) = xOverY (W.map g)) (haz : a (zOverY W) = zOverY (W.map g))
    [IsLocalRing T'] [IsAdicComplete (maximalIdeal T') T']
    (q q' : Spec (CommRingCat.of T') ⟶ projModelCR W)
    (hq : q ≫ projModelStrCR W = Spec.map (CommRingCat.ofHom g))
    (hq' : q' ≫ projModelStrCR W = Spec.map (CommRingCat.ofHom g))
    (χ χ' : OriginChartRing W →+* T')
    (hχ : q = Spec.map (CommRingCat.ofHom χ) ≫ originChartι W)
    (hχ' : q' = Spec.map (CommRingCat.ofHom χ') ≫ originChartι W)
    (h₁ : -(χ (xOverY W)) ∈ maximalIdeal T') (h₂ : -(χ (zOverY W)) ∈ maximalIdeal T')
    (h₁' : -(χ' (xOverY W)) ∈ maximalIdeal T') (h₂' : -(χ' (zOverY W)) ∈ maximalIdeal T')
    (h : -(χ (xOverY W)) = -(χ' (xOverY W))) :
    q = q' := by
  obtain ⟨S, hS⟩ := exists_section_comp_projMap_eq W g φ hφ hcoef q hq
  obtain ⟨S', hS'⟩ := exists_section_comp_projMap_eq W g φ hφ hcoef q' hq'
  obtain ⟨ψ, hψ, hψa⟩ := exists_eq_comp_originChartι_of_comp_projMap_eq W g φ hφ hcoef a ha S.1 χ (by rw [hS, hχ])
  obtain ⟨ψ', hψ', hψ'a⟩ :=
    exists_eq_comp_originChartι_of_comp_projMap_eq W g φ hφ hcoef a ha S'.1 χ' (by rw [hS', hχ'])
  have hp : originParam ψ = -(χ (xOverY W)) := by
    show -(ψ (xOverY (W.map g))) = -(χ (xOverY W))
    rw [← hax, ← hψa, RingHom.comp_apply]
  have hw : originW ψ = -(χ (zOverY W)) := by
    show -(ψ (zOverY (W.map g))) = -(χ (zOverY W))
    rw [← haz, ← hψa, RingHom.comp_apply]
  have hp' : originParam ψ' = -(χ' (xOverY W)) := by
    show -(ψ' (xOverY (W.map g))) = -(χ' (xOverY W))
    rw [← hax, ← hψ'a, RingHom.comp_apply]
  have hw' : originW ψ' = -(χ' (zOverY W)) := by
    show -(ψ' (zOverY (W.map g))) = -(χ' (zOverY W))
    rw [← haz, ← hψ'a, RingHom.comp_apply]
  have hred : ReducesToOrigin S ψ (maximalIdeal T') := ⟨hψ, by rw [hp]; exact h₁, by rw [hw]; exact h₂⟩
  have hred' : ReducesToOrigin S' ψ' (maximalIdeal T') := ⟨hψ', by rw [hp']; exact h₁', by rw [hw']; exact h₂'⟩
  have hSS' : S = S' :=
    (WeierstrassCurve.DrinfeldGlobal.section_eq_of_reducesToOrigin_of_originParam_eq (W.map g) S S' ψ ψ'
      hred hred' (by rw [hp, hp', h])).1
  rw [← hS, ← hS', hSS']

theorem exists_point_origin (W : WeierstrassCurve.Projective T) (g : T →+* T')
    (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map g))
    (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map g)) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ)
    (hcoef : IsCoefficientHom W g φ)
    (a : OriginChartRing W →+* OriginChartRing (W.map g))
    (ha : originChartι (W.map g) ≫ Proj.map φ hφ = Spec.map (CommRingCat.ofHom a) ≫ originChartι W)
    (hax : a (xOverY W) = xOverY (W.map g)) (haz : a (zOverY W) = zOverY (W.map g))
    [IsLocalRing T'] [IsAdicComplete (maximalIdeal T') T']
    (z : T') (hz : z ∈ maximalIdeal T') :
    ∃ q : Spec (CommRingCat.of T') ⟶ projModelCR W,
      q ≫ projModelStrCR W = Spec.map (CommRingCat.ofHom g) ∧
      ∃ χ : OriginChartRing W →+* T', q = Spec.map (CommRingCat.ofHom χ) ≫ originChartι W ∧
        -(χ (xOverY W)) = z ∧ -(χ (zOverY W)) ∈ maximalIdeal T' := by
  obtain ⟨P, ψ, ⟨hψ, -, hw⟩, hz'⟩ :=
    WeierstrassCurve.DrinfeldGlobal.exists_section_reducesToOrigin_originParam_eq (W.map g) z hz
  have hψ' : P.1 = Spec.map (CommRingCat.ofHom ψ) ≫ originChartι (W.map g) := hψ
  refine ⟨P.1 ≫ Proj.map φ hφ, section_comp_projMap_comp_str W g φ hφ hcoef P, ψ.comp a, ?_, ?_, ?_⟩
  · rw [hψ', Category.assoc, ha, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  · show -(ψ (a (xOverY W))) = z
    rw [hax]; exact hz'
  · show -(ψ (a (zOverY W))) ∈ maximalIdeal T'
    rw [haz]; exact hw

theorem exists_originChart_of_reduction (W : WeierstrassCurve.Projective T) (g : T →+* T')
    (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map g))
    (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map g)) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ)
    (hcoef : IsCoefficientHom W g φ)
    (a : OriginChartRing W →+* OriginChartRing (W.map g))
    (ha : originChartι (W.map g) ≫ Proj.map φ hφ = Spec.map (CommRingCat.ofHom a) ≫ originChartι W)
    (hax : a (xOverY W) = xOverY (W.map g)) (haz : a (zOverY W) = zOverY (W.map g))
    [IsLocalRing T'] {K : Type} [Field K] (π : T' →+* K) (hπ : RingHom.ker π = maximalIdeal T')
    (q : Spec (CommRingCat.of T') ⟶ projModelCR W)
    (hq : q ≫ projModelStrCR W = Spec.map (CommRingCat.ofHom g))
    (χ₀ : OriginChartRing W →+* K)
    (h₀ : Spec.map (CommRingCat.ofHom π) ≫ q = Spec.map (CommRingCat.ofHom χ₀) ≫ originChartι W)
    (hx : χ₀ (xOverY W) = 0) (hz : χ₀ (zOverY W) = 0) :
    ∃ χ : OriginChartRing W →+* T', q = Spec.map (CommRingCat.ofHom χ) ≫ originChartι W ∧
      -(χ (xOverY W)) ∈ maximalIdeal T' ∧ -(χ (zOverY W)) ∈ maximalIdeal T' := by
  obtain ⟨S, hS⟩ := exists_section_comp_projMap_eq W g φ hφ hcoef q hq
  obtain ⟨χbar, hχbar, hχbara⟩ := exists_eq_comp_originChartι_of_comp_projMap_eq W g φ hφ hcoef a ha
    (Spec.map (CommRingCat.ofHom π) ≫ S.1) χ₀ (by rw [Category.assoc, hS, h₀])
  have hbx : χbar (xOverY (W.map g)) = 0 := by rw [← hax, ← RingHom.comp_apply, hχbara]; exact hx
  have hbz : χbar (zOverY (W.map g)) = 0 := by rw [← haz, ← RingHom.comp_apply, hχbara]; exact hz
  obtain ⟨ψ, ⟨hψ, hp, hw⟩, -⟩ :=
    WeierstrassCurve.DrinfeldGlobal.exists_reducesToOrigin_of_specMap_comp_eq_originChart (W.map g) S π hπ
      χbar hχbar hbx hbz
  have hψ' : S.1 = Spec.map (CommRingCat.ofHom ψ) ≫ originChartι (W.map g) := hψ
  refine ⟨ψ.comp a, ?_, ?_, ?_⟩
  · rw [← hS, hψ', Category.assoc, ha, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  · show -(ψ (a (xOverY W))) ∈ maximalIdeal T'
    rw [hax]; exact hp
  · show -(ψ (a (zOverY W))) ∈ maximalIdeal T'
    rw [haz]; exact hw

end Origin

section Core

variable (k : Type) [Field k]

theorem core_affine (W : WeierstrassCurve k) (hΔ : W.Δ ≠ 0)
    (s₀ : Spec (CommRingCat.of k) ⟶ projModelCR W) (hs₀ : s₀ ≫ projModelStrCR W = 𝟙 _)
    (x₀ y₀ : k) (h₀ : IsSectionThrough (⟨s₀, hs₀⟩ : Section W) x₀ y₀) :
    ∃ q₁ : Spec (CommRingCat.of (DualNumber k)) ⟶ projModelCR W,
      q₁ ≫ projModelStrCR W = Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) ∧
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ q₁ = s₀ ∧
      q₁ ≠ Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) ≫ s₀ ∧
      ∀ q : Spec (CommRingCat.of (DualNumber k)) ⟶ projModelCR W,
        q ≫ projModelStrCR W = Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) →
        Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ q = s₀ →
        ∃ c : k, q = Spec.map (CommRingCat.ofHom ((TrivSqZeroExt.map (c • (LinearMap.id : k →ₗ[k] k))).toRingHom)) ≫ q₁ := by
  classical
  obtain ⟨φ, hφ, hcoef⟩ := WeierstrassProjModel.exists_isCoefficientHom W (algebraMap k (DualNumber k))
  obtain ⟨a, ha, hax, hay⟩ :=
    WeierstrassCurve.DrinfeldGlobal.exists_zChartIota_comp_projMap_eq_specMap_comp_zChartIota W (algebraMap k (DualNumber k)) φ hφ hcoef
  obtain ⟨χ₀, hχ₀, hχ₀x, hχ₀y⟩ := h₀
  have hχ₀' : s₀ = Spec.map (CommRingCat.ofHom χ₀) ≫ zChartι W := hχ₀
  have hx₀ : χ₀ (xOverZ W) = x₀ := hχ₀x
  have hy₀ : χ₀ (yOverZ W) = y₀ := hχ₀y

  have hE₀ : W.toAffine.Equation x₀ y₀ :=
    ((WeierstrassCurve.DrinfeldGlobal.equation_iff_exists_isSectionThrough_and_eq_iff_of_isSectionThrough
      W).1 x₀ y₀).mpr ⟨⟨s₀, hs₀⟩, χ₀, hχ₀, hχ₀x, hχ₀y⟩
  obtain ⟨v, hv0, hv⟩ :=
    WeierstrassCurve.Affine.exists_ne_zero_forall_equation_dualNumber_iff W hΔ x₀ y₀ hE₀

  obtain ⟨x₁, hx₁f, hx₁s⟩ : ∃ x₁ : (DualNumber k), x₁.fst = x₀ ∧ x₁.snd = v.1 :=
    ⟨TrivSqZeroExt.inl x₀ + TrivSqZeroExt.inr v.1, by simp, by simp⟩
  obtain ⟨y₁, hy₁f, hy₁s⟩ : ∃ y₁ : (DualNumber k), y₁.fst = y₀ ∧ y₁.snd = v.2 :=
    ⟨TrivSqZeroExt.inl y₀ + TrivSqZeroExt.inr v.2, by simp, by simp⟩
  have hE₁ : (W.map (algebraMap k (DualNumber k))).toAffine.Equation x₁ y₁ :=
    (hv x₁ y₁ hx₁f hy₁f).mpr ⟨1, by rw [hx₁s, one_mul], by rw [hy₁s, one_mul]⟩
  obtain ⟨q₁, hq₁str, ρ₁, hq₁, hρ₁x, hρ₁y⟩ := exists_point_zChart W (algebraMap k (DualNumber k)) φ hφ hcoef a ha hax hay x₁ y₁ hE₁
  refine ⟨q₁, hq₁str, ?_, ?_, ?_⟩
  ·
    have hT : (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ q₁) ≫ projModelStrCR W = 𝟙 _ := by
      rw [Category.assoc, hq₁str, specMap_fstHom_comp_specMap_algebraMap]
    have hthr : IsSectionThrough (⟨Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ q₁, hT⟩ : Section W) x₀ y₀ := by
      refine ⟨(TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ₁, ?_, ?_, ?_⟩
      · show Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ q₁ = Spec.map (CommRingCat.ofHom ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ₁)) ≫ zChartι W
        rw [hq₁, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
      · show (TrivSqZeroExt.fstHom k k k).toRingHom (ρ₁ (xOverZ W)) = x₀
        rw [hρ₁x, fstHom_apply', hx₁f]
      · show (TrivSqZeroExt.fstHom k k k).toRingHom (ρ₁ (yOverZ W)) = y₀
        rw [hρ₁y, fstHom_apply', hy₁f]
    have e := ((WeierstrassCurve.DrinfeldGlobal.equation_iff_exists_isSectionThrough_and_eq_iff_of_isSectionThrough
      W).2 _ ⟨s₀, hs₀⟩ x₀ y₀ x₀ y₀ hthr ⟨χ₀, hχ₀, hχ₀x, hχ₀y⟩).mpr ⟨rfl, rfl⟩
    exact congrArg Subtype.val e
  ·
    intro heq
    have e : Spec.map (CommRingCat.ofHom ρ₁) ≫ zChartι W =
        Spec.map (CommRingCat.ofHom (((algebraMap k (DualNumber k))).comp χ₀)) ≫ zChartι W := by
      rw [← hq₁, heq, hχ₀', ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have hρ := eq_of_specMap_comp_zChartι_eq W _ _ e
    apply hv0
    have h1 : v.1 = 0 := by
      rw [← hx₁s, ← hρ₁x, hρ, RingHom.comp_apply, algebraMap_dualNumber_snd]
    have h2 : v.2 = 0 := by
      rw [← hy₁s, ← hρ₁y, hρ, RingHom.comp_apply, algebraMap_dualNumber_snd]
    exact Prod.ext h1 h2
  ·
    intro q hqstr hq0
    obtain ⟨ρ, hρ, hπx, hπy, hE⟩ := exists_zChart_of_reduction W (algebraMap k (DualNumber k)) φ hφ hcoef a ha hax hay (TrivSqZeroExt.fstHom k k k).toRingHom
      (ker_fstHom_eq_maximalIdeal k) q hqstr χ₀ (by rw [hq0, hχ₀'])
    rw [hx₀, fstHom_apply'] at hπx
    rw [hy₀, fstHom_apply'] at hπy
    obtain ⟨c, hcx, hcy⟩ := (hv (ρ (xOverZ W)) (ρ (yOverZ W)) hπx hπy).mp hE
    refine ⟨c, eq_of_zChart_coords_eq W (algebraMap k (DualNumber k)) φ hφ hcoef a ha hax hay q _ hqstr ?_ ρ (((TrivSqZeroExt.map (c • (LinearMap.id : k →ₗ[k] k))).toRingHom).comp ρ₁) hρ ?_ ?_ ?_⟩
    · rw [Category.assoc, hq₁str, specMap_mapSmul_comp_specMap_algebraMap]
    · rw [hq₁, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    · rw [RingHom.comp_apply, hρ₁x]
      refine TrivSqZeroExt.ext ?_ ?_
      · rw [mapSmul_fst, hx₁f, hπx]
      · rw [mapSmul_snd, hx₁s, hcx]
    · rw [RingHom.comp_apply, hρ₁y]
      refine TrivSqZeroExt.ext ?_ ?_
      · rw [mapSmul_fst, hy₁f, hπy]
      · rw [mapSmul_snd, hy₁s, hcy]

theorem core_origin (W : WeierstrassCurve k)
    (s₀ : Spec (CommRingCat.of k) ⟶ projModelCR W) (hs₀ : s₀ ≫ projModelStrCR W = 𝟙 _)
    (χ₀ : OriginChartRing W →+* k) (hχ₀ : s₀ = Spec.map (CommRingCat.ofHom χ₀) ≫ originChartι W)
    (hχ₀x : χ₀ (xOverY W) = 0) (hχ₀z : χ₀ (zOverY W) = 0) :
    ∃ q₁ : Spec (CommRingCat.of (DualNumber k)) ⟶ projModelCR W,
      q₁ ≫ projModelStrCR W = Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) ∧
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ q₁ = s₀ ∧
      q₁ ≠ Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) ≫ s₀ ∧
      ∀ q : Spec (CommRingCat.of (DualNumber k)) ⟶ projModelCR W,
        q ≫ projModelStrCR W = Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) →
        Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ q = s₀ →
        ∃ c : k, q = Spec.map (CommRingCat.ofHom ((TrivSqZeroExt.map (c • (LinearMap.id : k →ₗ[k] k))).toRingHom)) ≫ q₁ := by
  classical
  haveI := isAdicComplete_dualNumber k
  haveI := isAdicComplete_field k
  obtain ⟨φ, hφ, hcoef⟩ := WeierstrassProjModel.exists_isCoefficientHom W (algebraMap k (DualNumber k))
  obtain ⟨a, ha, hax, haz⟩ := exists_originChartι_comp_projMap W (algebraMap k (DualNumber k)) φ hφ hcoef
  obtain ⟨q₁, hq₁str, χ₁, hq₁, hpar₁, hW₁⟩ :=
    exists_point_origin W (algebraMap k (DualNumber k)) φ hφ hcoef a ha hax haz DualNumber.eps (eps_mem_maximalIdeal k)
  have hW₁' : (-(χ₁ (zOverY W))).fst = 0 := (mem_maximalIdeal_dualNumber_iff _).mp hW₁
  refine ⟨q₁, hq₁str, ?_, ?_, ?_⟩
  ·
    have hT : (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ q₁) ≫ projModelStrCR W = 𝟙 _ := by
      rw [Category.assoc, hq₁str, specMap_fstHom_comp_specMap_algebraMap]
    have hparT : originParam ((TrivSqZeroExt.fstHom k k k).toRingHom.comp χ₁) = 0 := by
      show -((TrivSqZeroExt.fstHom k k k).toRingHom (χ₁ (xOverY W))) = 0
      rw [← map_neg, hpar₁]
      exact fstHom_eps k
    have hwT : originW ((TrivSqZeroExt.fstHom k k k).toRingHom.comp χ₁) = 0 := by
      show -((TrivSqZeroExt.fstHom k k k).toRingHom (χ₁ (zOverY W))) = 0
      rw [← map_neg, fstHom_apply']
      exact hW₁'
    have hred : ReducesToOrigin (⟨Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ q₁, hT⟩ : Section W) ((TrivSqZeroExt.fstHom k k k).toRingHom.comp χ₁)
        (maximalIdeal k) := by
      refine ⟨?_, ?_, ?_⟩
      · show Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ q₁ =
          Spec.map (CommRingCat.ofHom ((TrivSqZeroExt.fstHom k k k).toRingHom.comp χ₁)) ≫ originChartι W
        rw [hq₁, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
      · rw [hparT]; exact Ideal.zero_mem _
      · rw [hwT]; exact Ideal.zero_mem _
    have hpar₀ : originParam χ₀ = 0 := by
      show -(χ₀ (xOverY W)) = 0
      rw [hχ₀x, neg_zero]
    have hw₀ : originW χ₀ = 0 := by
      show -(χ₀ (zOverY W)) = 0
      rw [hχ₀z, neg_zero]
    have hred₀ : ReducesToOrigin (⟨s₀, hs₀⟩ : Section W) χ₀ (maximalIdeal k) :=
      ⟨hχ₀, by rw [hpar₀]; exact Ideal.zero_mem _, by rw [hw₀]; exact Ideal.zero_mem _⟩
    have e := (WeierstrassCurve.DrinfeldGlobal.section_eq_of_reducesToOrigin_of_originParam_eq W _ _ _ _
      hred hred₀ (by rw [hparT, hpar₀])).1
    exact congrArg Subtype.val e
  ·
    intro heq
    have e : Spec.map (CommRingCat.ofHom χ₁) ≫ originChartι W =
        Spec.map (CommRingCat.ofHom (((algebraMap k (DualNumber k))).comp χ₀)) ≫ originChartι W := by
      rw [← hq₁, heq, hχ₀, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have hχ := eq_of_specMap_comp_originChartι_eq W _ _ e
    apply eps_ne_zero k
    rw [← hpar₁, hχ, RingHom.comp_apply, hχ₀x, map_zero, neg_zero]
  ·
    intro q hqstr hq0
    obtain ⟨χ, hχq, hp, hw⟩ := exists_originChart_of_reduction W (algebraMap k (DualNumber k)) φ hφ hcoef a ha hax haz (TrivSqZeroExt.fstHom k k k).toRingHom
      (ker_fstHom_eq_maximalIdeal k) q hqstr χ₀ (by rw [hq0, hχ₀]) hχ₀x hχ₀z
    obtain ⟨z, hzdef⟩ : ∃ z : (DualNumber k), -(χ (xOverY W)) = z := ⟨_, rfl⟩
    have hzf : z.fst = 0 := by rw [← hzdef]; exact (mem_maximalIdeal_dualNumber_iff _).mp hp
    refine ⟨z.snd, eq_of_originParam_eq W (algebraMap k (DualNumber k)) φ hφ hcoef a ha hax haz q _ hqstr ?_ χ
      (((TrivSqZeroExt.map (z.snd • (LinearMap.id : k →ₗ[k] k))).toRingHom).comp χ₁) hχq ?_ hp hw ?_ ?_ ?_⟩
    · rw [Category.assoc, hq₁str, specMap_mapSmul_comp_specMap_algebraMap]
    · rw [hq₁, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    · rw [mem_maximalIdeal_dualNumber_iff, RingHom.comp_apply, ← map_neg ((TrivSqZeroExt.map (z.snd • (LinearMap.id : k →ₗ[k] k))).toRingHom), mapSmul_fst, hpar₁]
      exact DualNumber.fst_eps
    · rw [mem_maximalIdeal_dualNumber_iff, RingHom.comp_apply, ← map_neg ((TrivSqZeroExt.map (z.snd • (LinearMap.id : k →ₗ[k] k))).toRingHom), mapSmul_fst]
      exact hW₁'
    · rw [hzdef, RingHom.comp_apply, ← map_neg ((TrivSqZeroExt.map (z.snd • (LinearMap.id : k →ₗ[k] k))).toRingHom), hpar₁]
      refine TrivSqZeroExt.ext ?_ ?_
      · rw [mapSmul_fst, hzf, DualNumber.fst_eps]
      · rw [mapSmul_snd, DualNumber.snd_eps, mul_one]

theorem core (W : WeierstrassCurve k) (hΔ : W.Δ ≠ 0)
    (s₀ : Spec (CommRingCat.of k) ⟶ projModelCR W) (hs₀ : s₀ ≫ projModelStrCR W = 𝟙 _) :
    ∃ q₁ : Spec (CommRingCat.of (DualNumber k)) ⟶ projModelCR W,
      q₁ ≫ projModelStrCR W = Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) ∧
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ q₁ = s₀ ∧
      q₁ ≠ Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) ≫ s₀ ∧
      ∀ q : Spec (CommRingCat.of (DualNumber k)) ⟶ projModelCR W,
        q ≫ projModelStrCR W = Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) →
        Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ q = s₀ →
        ∃ c : k, q = Spec.map (CommRingCat.ofHom ((TrivSqZeroExt.map (c • (LinearMap.id : k →ₗ[k] k))).toRingHom)) ≫ q₁ := by
  rcases WeierstrassCurve.DrinfeldGlobal.exists_isSectionThrough_or_exists_reducesToOrigin W ⟨s₀, hs₀⟩ with
    ⟨x₀, y₀, h⟩ | ⟨χ₀, hχ₀, hp, hw⟩
  · exact core_affine k W hΔ s₀ hs₀ x₀ y₀ h
  · have hp' : originParam χ₀ = 0 := (mem_maximalIdeal_field_iff _).mp hp
    have hw' : originW χ₀ = 0 := (mem_maximalIdeal_field_iff _).mp hw
    have hx : χ₀ (xOverY W) = 0 := by
      have e : -(χ₀ (xOverY W)) = 0 := hp'
      rwa [neg_eq_zero] at e
    have hz : χ₀ (zOverY W) = 0 := by
      have e : -(χ₀ (zOverY W)) = 0 := hw'
      rwa [neg_eq_zero] at e
    exact core_origin k W s₀ hs₀ χ₀ hχ₀ hx hz

end Core

end LiftsLineAux
p2m_reactivate "P2MW.S_WeierstrassProjModel_exists_ne_forall_exists_eq_specMap_map_smul_comp_of_specMap_fstHom_comp_eq.LiftsLineAux"

open LiftsLineAux

theorem solution
    (B : Type) [CommRing B] (V : WeierstrassCurve B) (hΔ : IsUnit V.Δ) (k : Type) [Field k] (f : B →+* k)
    (Q₀ : SchemeHomOver (Spec.map (CommRingCat.ofHom f)) (projModelStrCR V)) :
    ∃ Q₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom ((algebraMap k (DualNumber k)).comp f))) (projModelStrCR V),
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ Q₁.1 = Q₀.1 ∧
      Q₁.1 ≠ Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) ≫ Q₀.1 ∧
      ∀ Q : SchemeHomOver (Spec.map (CommRingCat.ofHom ((algebraMap k (DualNumber k)).comp f))) (projModelStrCR V),
        Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ Q.1 = Q₀.1 →
        ∃ c : k, Q.1 = Spec.map (CommRingCat.ofHom
          (TrivSqZeroExt.map (c • (LinearMap.id : k →ₗ[k] k))).toRingHom) ≫ Q₁.1 := by
  classical
  obtain ⟨φ, hφ, hcoef⟩ := WeierstrassProjModel.exists_isCoefficientHom V f
  have hpb := WeierstrassCurve.DrinfeldGlobal.isPullback_projMap_of_isCoefficientHom V f φ hφ hcoef
  have hΔ' : (V.map f).Δ ≠ 0 := by
    rw [WeierstrassCurve.map_Δ]; exact (hΔ.map f).ne_zero

  have w₀ : Q₀.1 ≫ projModelStrCR V = 𝟙 _ ≫ Spec.map (CommRingCat.ofHom f) := by
    rw [Category.id_comp]; exact Q₀.2
  obtain ⟨s₀, hs₀P, hs₀⟩ : ∃ s₀ : Spec (CommRingCat.of k) ⟶ projModelCR (V.map f),
      s₀ ≫ Proj.map φ hφ = Q₀.1 ∧ s₀ ≫ projModelStrCR (V.map f) = 𝟙 _ :=
    ⟨hpb.lift Q₀.1 (𝟙 _) w₀, hpb.lift_fst _ _ _, hpb.lift_snd _ _ _⟩
  obtain ⟨q₁, hq₁str, h1, h2, h3⟩ := core k (V.map f) hΔ' s₀ hs₀
  have hιf : Spec.map (CommRingCat.ofHom ((algebraMap k (DualNumber k)).comp f)) =
      Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) ≫ Spec.map (CommRingCat.ofHom f) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
  refine ⟨⟨q₁ ≫ Proj.map φ hφ, ?_⟩, ?_, ?_, ?_⟩
  · rw [Category.assoc, hpb.w, ← Category.assoc, hq₁str, hιf]
  · show Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ q₁ ≫ Proj.map φ hφ = Q₀.1
    rw [← Category.assoc, h1, hs₀P]
  · intro heq
    apply h2
    apply hpb.hom_ext
    · rw [Category.assoc, hs₀P]; exact heq
    · rw [hq₁str, Category.assoc, hs₀, Category.comp_id]
  · intro Q hQ
    have wQ : Q.1 ≫ projModelStrCR V =
        Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) ≫ Spec.map (CommRingCat.ofHom f) := by
      rw [Q.2, hιf]
    obtain ⟨q, hqP, hqstr⟩ : ∃ q : Spec (CommRingCat.of (DualNumber k)) ⟶ projModelCR (V.map f),
        q ≫ Proj.map φ hφ = Q.1 ∧ q ≫ projModelStrCR (V.map f) =
          Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) :=
      ⟨hpb.lift Q.1 _ wQ, hpb.lift_fst _ _ _, hpb.lift_snd _ _ _⟩
    have hq0 : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ q = s₀ := by
      apply hpb.hom_ext
      · rw [Category.assoc, hqP, hQ, hs₀P]
      · rw [Category.assoc, hqstr, hs₀, specMap_fstHom_comp_specMap_algebraMap]
    obtain ⟨c, hc⟩ := h3 q hqstr hq0
    refine ⟨c, ?_⟩
    show Q.1 = Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map (c • (LinearMap.id : k →ₗ[k] k))).toRingHom) ≫
      q₁ ≫ Proj.map φ hφ
    rw [← hqP, hc, Category.assoc]

end S_WeierstrassProjModel_exists_ne_forall_exists_eq_specMap_map_smul_comp_of_specMap_fstHom_comp_eq
end P2MW
export P2MW.S_WeierstrassProjModel_exists_ne_forall_exists_eq_specMap_map_smul_comp_of_specMap_fstHom_comp_eq (solution)
