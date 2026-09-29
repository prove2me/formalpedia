-- Prove2me | solution 1 for WeierstrassProjModel.exists_ringEquiv_zChartRing_of_iso_of_kwZeroSect_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/10421fac-f8f8-5318-8fa5-88470abe36a1

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Theorems.Thm_WeierstrassProjModel_isOriginChartSection_kwZeroSect_kwYChartEval
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_ker_eq_span_of_originChartRing
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_originChart_rel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_exists_ringEquiv_zChartRing_of_iso_of_kwZeroSect_comp_eq

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

namespace WMLocal

section Cover

open MvPolynomial TopologicalSpace

variable {R : Type} [CommRing R] (V : WeierstrassCurve.Projective R)

theorem polynomial_add_X0_cube :
    V.polynomial + X 0 ^ 3 = X 2 * (X 1 ^ 2 + C V.a₁ * X 0 * X 1 + C V.a₃ * X 1 * X 2
      - C V.a₂ * X 0 ^ 2 - C V.a₄ * X 0 * X 2 - C V.a₆ * X 2 ^ 2) := by
  rw [WeierstrassCurve.Projective.polynomial]
  ring

theorem not_mem_and_mem (x : Proj (projModelGradingCR V)) :
    ¬ (coord V 1 ∈ x.asHomogeneousIdeal ∧ coord V 2 ∈ x.asHomogeneousIdeal) := by
  rintro ⟨h1, h2⟩
  have hpoly : Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal V.polynomial = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  have hid := congrArg (Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal) (polynomial_add_X0_cube V)
  rw [map_add, map_mul, map_pow, hpoly, zero_add] at hid
  have h0 : coord V 0 ∈ x.asHomogeneousIdeal.toIdeal := by
    apply x.isPrime.mem_of_pow_mem 3
    change Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal (X 0 : MvPolynomial (Fin 3) R) ^ 3 ∈ _
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

theorem mem_basicOpen_or (x : Proj (projModelGradingCR V)) :
    x ∈ Proj.basicOpen (projModelGradingCR V) (coord V 1) ∨ x ∈ Proj.basicOpen (projModelGradingCR V) (coord V 2) := by
  rw [Proj.mem_basicOpen, Proj.mem_basicOpen]
  by_cases h1 : coord V 1 ∈ x.asHomogeneousIdeal
  · exact Or.inr fun h2 => not_mem_and_mem V x ⟨h1, h2⟩
  · exact Or.inl h1

theorem isLocalizationElem_eq_zOverY :
    Away.isLocalizationElem (coord_mem V 1) (coord_mem V 2) = zOverY V := by
  apply HomogeneousLocalization.val_injective
  simp [Away.isLocalizationElem, zOverY, Away.mk, HomogeneousLocalization.val_mk, pow_one]

end Cover

section ZeroSection

variable {T : Type} [CommRing T] (W : WeierstrassCurve T)

noncomputable abbrev cY : T →+* OriginChartRing W.toProjective :=
  (fromZeroRingHom (projModelGradingCR W.toProjective) _).comp (algebraMap T ((projModelGradingCR W.toProjective) 0))

theorem not_mem_basicOpen_iff_mem_range_kwZeroSect (x : ↥(projModelCR W.toProjective)) :
    x ∉ Proj.basicOpen (projModelGradingCR W.toProjective) (coord W.toProjective 2) ↔
      x ∈ Set.range (kwZeroSect T W).1 := by
  obtain ⟨hO, hχx, hχz⟩ := WeierstrassProjModel.isOriginChartSection_kwZeroSect_kwYChartEval W.toProjective
  have hO' : (kwZeroSect T W).1 =
      Spec.map (CommRingCat.ofHom (kwYChartEval T W)) ≫ originChartι W.toProjective := hO
  let χ₀ := kwYChartEval T W
  have hχc : ∀ t, χ₀ (cY W t) = t := fun t => RingHom.congr_fun (kwYChartEval_section T W) t
  have hpre : originChartι W.toProjective ⁻¹ᵁ Proj.basicOpen (projModelGradingCR W.toProjective) (coord W.toProjective 2) =
      PrimeSpectrum.basicOpen (zOverY W.toProjective) := by
    rw [Proj.awayι_preimage_basicOpen (projModelGradingCR W.toProjective) (coord_mem W.toProjective 1) one_pos
      (coord_mem W.toProjective 2) one_pos, isLocalizationElem_eq_zOverY]
  constructor
  · intro hx

    have hx1 : x ∈ (originChartι W.toProjective).opensRange := by
      rw [Proj.opensRange_awayι]
      exact (mem_basicOpen_or W.toProjective x).elim id fun h => absurd h hx
    obtain ⟨p, rfl⟩ := hx1

    have hz : zOverY W.toProjective ∈ p.asIdeal := by
      by_contra h
      have hp : p ∈ originChartι W.toProjective ⁻¹ᵁ
          Proj.basicOpen (projModelGradingCR W.toProjective) (coord W.toProjective 2) := by
        rw [hpre]; exact (PrimeSpectrum.mem_basicOpen _ _).mpr h
      exact hx hp
    have hrel := by
      letI : Algebra T (OriginChartRing W.toProjective) := (cY W).toAlgebra
      exact WeierstrassCurve.DrinfeldGlobal.originChart_rel W (RingHom.id _) (fun t => rfl)
    simp only [RingHom.id_apply] at hrel
    have hx3 : xOverY W.toProjective ^ 3 ∈ p.asIdeal := by
      letI : Algebra T (OriginChartRing W.toProjective) := (cY W).toAlgebra
      have : xOverY W.toProjective ^ 3 =
          zOverY W.toProjective * (1 + algebraMap T _ W.a₁ * xOverY W.toProjective +
            algebraMap T _ W.a₃ * zOverY W.toProjective - algebraMap T _ W.a₂ * xOverY W.toProjective ^ 2 -
            algebraMap T _ W.a₄ * xOverY W.toProjective * zOverY W.toProjective -
            algebraMap T _ W.a₆ * zOverY W.toProjective ^ 2) := by
        linear_combination (-1 : OriginChartRing W.toProjective) * hrel
      rw [this]
      exact Ideal.mul_mem_right _ _ hz
    have hxm : xOverY W.toProjective ∈ p.asIdeal := p.isPrime.mem_of_pow_mem 3 hx3

    have hker : RingHom.ker χ₀ ≤ p.asIdeal := by
      rw [WeierstrassCurve.DrinfeldGlobal.ker_eq_span_of_originChartRing W χ₀ hχc, hχx, hχz, map_zero, map_zero,
        sub_zero, sub_zero, Ideal.span_le]
      rintro a (rfl | rfl)
      · exact hxm
      · exact hz
    let t : ↥(Spec (CommRingCat.of T)) := Spec.map (CommRingCat.ofHom (cY W)) p
    have hpt : Spec.map (CommRingCat.ofHom χ₀) t = p := by
      apply PrimeSpectrum.ext
      change Ideal.comap χ₀ (Ideal.comap (cY W) p.asIdeal) = p.asIdeal
      ext a
      simp only [Ideal.mem_comap]
      have hdiff : a - cY W (χ₀ a) ∈ p.asIdeal := hker (by rw [RingHom.mem_ker, map_sub, hχc, sub_self])
      constructor
      · intro h
        have := p.asIdeal.add_mem hdiff h
        rwa [sub_add_cancel] at this
      · intro h
        have := p.asIdeal.sub_mem h hdiff
        rwa [sub_sub_cancel] at this
    refine ⟨t, ?_⟩
    rw [hO', Scheme.Hom.comp_apply, hpt]
  · rintro ⟨t, rfl⟩ hmem
    rw [hO', Scheme.Hom.comp_apply] at hmem
    have : Spec.map (CommRingCat.ofHom χ₀) t ∈ originChartι W.toProjective ⁻¹ᵁ
        Proj.basicOpen (projModelGradingCR W.toProjective) (coord W.toProjective 2) := hmem
    rw [hpre] at this
    refine (PrimeSpectrum.mem_basicOpen _ _).mp this ?_
    change χ₀ (zOverY W.toProjective) ∈ t.asIdeal
    rw [hχz]
    exact Ideal.zero_mem _

end ZeroSection

section Restrict

variable {T : Type} [CommRing T] (W W' : WeierstrassCurve T)

noncomputable abbrev cZ : T →+* ZChartRing W.toProjective :=
  (fromZeroRingHom (projModelGradingCR W.toProjective) _).comp (algebraMap T ((projModelGradingCR W.toProjective) 0))

theorem zChartι_comp_projModelStrCR :
    zChartι W.toProjective ≫ projModelStrCR W.toProjective = Spec.map (CommRingCat.ofHom (cZ W)) := by
  simp only [projModelStrCR]
  rw [← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem preimage_opensRange_zChartι (Ψ : projModelCR W.toProjective ≅ projModelCR W'.toProjective)
    (hΨO : (kwZeroSect T W).1 ≫ Ψ.hom = (kwZeroSect T W').1) :
    Ψ.hom ⁻¹ᵁ (zChartι W'.toProjective).opensRange = (zChartι W.toProjective).opensRange := by
  ext x
  rw [Proj.opensRange_awayι, Proj.opensRange_awayι]
  change Ψ.hom x ∈ Proj.basicOpen (projModelGradingCR W'.toProjective) (coord W'.toProjective 2) ↔
    x ∈ Proj.basicOpen (projModelGradingCR W.toProjective) (coord W.toProjective 2)
  rw [← not_iff_not, not_mem_basicOpen_iff_mem_range_kwZeroSect W', not_mem_basicOpen_iff_mem_range_kwZeroSect W]
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_⟩
    have hinj : Function.Injective Ψ.hom := (Scheme.homeoOfIso Ψ).injective
    apply hinj
    rw [← ht, ← Scheme.Hom.comp_apply, hΨO]
  · rintro ⟨t, rfl⟩
    exact ⟨t, by rw [← Scheme.Hom.comp_apply, hΨO]⟩

theorem exists_ringEquiv_zChartRing_of_iso (Ψ : projModelCR W.toProjective ≅ projModelCR W'.toProjective)
    (hΨ : Ψ.hom ≫ projModelStrCR W'.toProjective = projModelStrCR W.toProjective)
    (hΨO : (kwZeroSect T W).1 ≫ Ψ.hom = (kwZeroSect T W').1) :
    ∃ e : ZChartRing W'.toProjective ≃+* ZChartRing W.toProjective,
      (∀ t : T, e (cZ W' t) = cZ W t) ∧
      Spec.map (CommRingCat.ofHom e.toRingHom) ≫ zChartι W'.toProjective = zChartι W.toProjective ≫ Ψ.hom := by

  have hrange : Set.range (zChartι W.toProjective ≫ Ψ.hom) = Set.range (zChartι W'.toProjective) := by
    have h := preimage_opensRange_zChartι W W' Ψ hΨO
    have hsurj : Function.Surjective Ψ.hom := (Scheme.homeoOfIso Ψ).surjective
    ext y
    constructor
    · rintro ⟨p, rfl⟩
      have : zChartι W.toProjective p ∈ Ψ.hom ⁻¹ᵁ (zChartι W'.toProjective).opensRange := by
        rw [h]; exact ⟨p, rfl⟩
      simpa [Scheme.Hom.comp_apply] using this
    · rintro ⟨p', rfl⟩
      obtain ⟨x, hx⟩ := hsurj (zChartι W'.toProjective p')
      have : x ∈ Ψ.hom ⁻¹ᵁ (zChartι W'.toProjective).opensRange := by
        show Ψ.hom x ∈ (zChartι W'.toProjective).opensRange
        rw [hx]; exact ⟨p', rfl⟩
      rw [h] at this
      obtain ⟨p, rfl⟩ := this
      exact ⟨p, by rw [Scheme.Hom.comp_apply, hx]⟩
  let δ : Spec (CommRingCat.of (ZChartRing W.toProjective)) ≅ Spec (CommRingCat.of (ZChartRing W'.toProjective)) :=
    IsOpenImmersion.isoOfRangeEq (zChartι W.toProjective ≫ Ψ.hom) (zChartι W'.toProjective) hrange
  have hδ : δ.hom ≫ zChartι W'.toProjective = zChartι W.toProjective ≫ Ψ.hom :=
    IsOpenImmersion.isoOfRangeEq_hom_fac _ _ hrange

  obtain ⟨φ₁, hφ₁⟩ := Spec.map_surjective δ.hom
  obtain ⟨φ₂, hφ₂⟩ := Spec.map_surjective δ.inv
  have h12 : φ₂ ≫ φ₁ = 𝟙 _ := Spec.map_injective (by rw [Spec.map_comp, hφ₁, hφ₂, δ.hom_inv_id, Spec.map_id])
  have h21 : φ₁ ≫ φ₂ = 𝟙 _ := Spec.map_injective (by rw [Spec.map_comp, hφ₁, hφ₂, δ.inv_hom_id, Spec.map_id])
  let e : ZChartRing W'.toProjective ≃+* ZChartRing W.toProjective :=
    RingEquiv.ofRingHom φ₁.hom φ₂.hom (RingHom.ext fun a => by simpa using CategoryTheory.congr_fun h12 a)
      (RingHom.ext fun a => by simpa using CategoryTheory.congr_fun h21 a)
  have he : CommRingCat.ofHom e.toRingHom = φ₁ := rfl
  refine ⟨e, ?_, by rw [he, hφ₁, hδ]⟩

  have h2 : Spec.map φ₁ ≫ Spec.map (CommRingCat.ofHom (cZ W')) = Spec.map (CommRingCat.ofHom (cZ W)) := by
    rw [← zChartι_comp_projModelStrCR W', hφ₁, ← Category.assoc, hδ, Category.assoc, hΨ, zChartι_comp_projModelStrCR W]
  have h3 : CommRingCat.ofHom (cZ W') ≫ φ₁ = CommRingCat.ofHom (cZ W) :=
    Spec.map_injective (by rw [Spec.map_comp]; exact h2)
  intro t
  have := congrArg (fun f : CommRingCat.of T ⟶ CommRingCat.of (ZChartRing W.toProjective) => f.hom t) h3
  simp at this
  exact this

end Restrict

end WMLocal

theorem solution
    (T : Type) [CommRing T] (W W' : WeierstrassCurve T)
    (Ψ : projModelCR W.toProjective ≅ projModelCR W'.toProjective)
    (hΨ : Ψ.hom ≫ projModelStrCR W'.toProjective = projModelStrCR W.toProjective)
    (hΨO : (kwZeroSect T W).1 ≫ Ψ.hom = (kwZeroSect T W').1) :
    ∃ e : ZChartRing W'.toProjective ≃+* ZChartRing W.toProjective,
      (∀ t : T, e (fromZeroRingHom (projModelGradingCR W'.toProjective) _ (algebraMap T ((projModelGradingCR W'.toProjective) 0) t)) =
        fromZeroRingHom (projModelGradingCR W.toProjective) _ (algebraMap T ((projModelGradingCR W.toProjective) 0) t)) ∧
      Spec.map (CommRingCat.ofHom e.toRingHom) ≫ zChartι W'.toProjective = zChartι W.toProjective ≫ Ψ.hom :=
  WMLocal.exists_ringEquiv_zChartRing_of_iso W W' Ψ hΨ hΨO

end S_WeierstrassProjModel_exists_ringEquiv_zChartRing_of_iso_of_kwZeroSect_comp_eq
end P2MW
export P2MW.S_WeierstrassProjModel_exists_ringEquiv_zChartRing_of_iso_of_kwZeroSect_comp_eq (solution)
