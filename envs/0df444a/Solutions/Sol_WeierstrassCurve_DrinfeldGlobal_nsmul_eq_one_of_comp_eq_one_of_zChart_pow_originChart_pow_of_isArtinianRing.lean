-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.nsmul_eq_one_of_comp_eq_one_of_zChart_pow_originChart_pow_of_isArtinianRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/c0da27d0-0cf5-5b65-b6f0-21312996fc0a

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_nsmul_eq_one_of_comp_originChartIota_of_pow_eq_zero_of_isAdicComplete
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_nsmul_eq_one_of_comp_eq_one_of_zChart_pow_originChart_pow_of_isArtinianRing
p2m_attr_erase "instance" "WeierstrassCurve.instIsCommFormalGroup"
p2m_attr_erase "simp" "MvPowerSeries.kw_coeff_pderiv FormalGroup.nthSeries_zero FormalGroup.evalNSMul_zero FormalGroup.DrinfeldLevel.mk.sizeOf_spec FormalGroup.DrinfeldLevel.mk.injEq WeierstrassCurve.wIter_zero FormalGroup.LawIso.mk.sizeOf_spec FormalGroup.LawHom.mk.sizeOf_spec FormalGroup.LawHom.mk.injEq FormalGroup.LawIso.mk.injEq WeierstrassProjModel.kw_lrThird_substHom_X"

set_option autoImplicit false

namespace R4S188bFrobKerLocal

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal HomogeneousLocalization HomogeneousIdealQuotientGrading CommRingCat NeronModelInfra

attribute [local instance] MvPolynomial.gradedAlgebra

variable {T : Type u} [CommRing T]

theorem mem_basicOpen_Y_or_Z (V : WeierstrassCurve T) (x : projModelCR V.toProjective) :
    x ∈ Proj.basicOpen (projModelGradingCR V.toProjective) (coord V.toProjective 1) ∨
      x ∈ Proj.basicOpen (projModelGradingCR V.toProjective) (coord V.toProjective 2) := by
  by_contra hcon
  rw [not_or, Proj.mem_basicOpen, Proj.mem_basicOpen, not_not, not_not] at hcon
  obtain ⟨hY, hZ⟩ := hcon
  have hprime := x.isPrime

  have key : (MvPolynomial.X 0 : MvPolynomial (Fin 3) T) ^ 3 =
      MvPolynomial.X 2 * (MvPolynomial.X 1 ^ 2 + MvPolynomial.C V.a₁ * MvPolynomial.X 0 * MvPolynomial.X 1
        + MvPolynomial.C V.a₃ * MvPolynomial.X 1 * MvPolynomial.X 2 - MvPolynomial.C V.a₂ * MvPolynomial.X 0 ^ 2
        - MvPolynomial.C V.a₄ * MvPolynomial.X 0 * MvPolynomial.X 2 - MvPolynomial.C V.a₆ * MvPolynomial.X 2 ^ 2)
      - V.toProjective.polynomial := by
    rw [WeierstrassCurve.Projective.polynomial]; ring
  have hpoly : Ideal.Quotient.mk (projModelHomogeneousIdealCR V.toProjective).toIdeal V.toProjective.polynomial = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (by rw [projModelHomogeneousIdealCR_toIdeal]; exact Ideal.subset_span rfl)
  have hX3 : coord V.toProjective 0 ^ 3 ∈ x.asHomogeneousIdeal.toIdeal := by
    have : coord V.toProjective 0 ^ 3 = coord V.toProjective 2 *
        Ideal.Quotient.mk (projModelHomogeneousIdealCR V.toProjective).toIdeal
          (MvPolynomial.X 1 ^ 2 + MvPolynomial.C V.a₁ * MvPolynomial.X 0 * MvPolynomial.X 1
            + MvPolynomial.C V.a₃ * MvPolynomial.X 1 * MvPolynomial.X 2 - MvPolynomial.C V.a₂ * MvPolynomial.X 0 ^ 2
            - MvPolynomial.C V.a₄ * MvPolynomial.X 0 * MvPolynomial.X 2 - MvPolynomial.C V.a₆ * MvPolynomial.X 2 ^ 2) := by
      change Ideal.Quotient.mk _ (MvPolynomial.X 0) ^ 3 = Ideal.Quotient.mk _ (MvPolynomial.X 2) * _
      rw [← map_pow, key, map_sub, hpoly, sub_zero, map_mul]
    rw [this]
    exact Ideal.mul_mem_right _ _ hZ
  have hX : coord V.toProjective 0 ∈ x.asHomogeneousIdeal.toIdeal := hprime.mem_of_pow_mem 3 hX3
  refine x.not_irrelevant_le ((kw_pbac_irrelevant_le_span_mk_X_CR T V.toProjective).trans (Ideal.span_le.mpr ?_))
  rintro _ ⟨i, rfl⟩
  fin_cases i
  exacts [hX, hY, hZ]

theorem isLocalizationElem_eq_yOverZ (V : WeierstrassCurve.Projective T) :
    Away.isLocalizationElem (coord_mem V 2) (coord_mem V 1) = yOverZ V := by
  apply HomogeneousLocalization.val_injective
  rw [yOverZ, Away.val_mk, Away.val_mk, pow_one]

theorem preimage_basicOpen_Y {q : ℕ} (hq : 0 < q) (V₁ V₂ : WeierstrassCurve T)
    (Φ : projModelCR V₁.toProjective ⟶ projModelCR V₂.toProjective)
    (hZ : ∃ ψ : ZChartRing V₂.toProjective →+* ZChartRing V₁.toProjective,
        ψ (yOverZ V₂.toProjective) = yOverZ V₁.toProjective ^ q ∧
        zChartι V₁.toProjective ≫ Φ = Spec.map (CommRingCat.ofHom ψ) ≫ zChartι V₂.toProjective)
    (hY : ∃ ψ : OriginChartRing V₂.toProjective →+* OriginChartRing V₁.toProjective,
        originChartι V₁.toProjective ≫ Φ = Spec.map (CommRingCat.ofHom ψ) ≫ originChartι V₂.toProjective) :
    Φ ⁻¹ᵁ (originChartι V₂.toProjective).opensRange = (originChartι V₁.toProjective).opensRange := by
  obtain ⟨ψZ, hψZ, hsqZ⟩ := hZ
  obtain ⟨ψY, hsqY⟩ := hY
  ext x
  constructor
  · intro hx
    change Φ x ∈ (originChartι V₂.toProjective).opensRange at hx
    rcases mem_basicOpen_Y_or_Z V₁ x with h | h
    · rwa [← Proj.opensRange_awayι _ _ (coord_mem V₁.toProjective 1) one_pos] at h
    · rw [← Proj.opensRange_awayι _ _ (coord_mem V₁.toProjective 2) one_pos] at h
      obtain ⟨p, rfl⟩ := Scheme.Hom.mem_opensRange.mp h

      have hΦ : Φ (zChartι V₁.toProjective p) = zChartι V₂.toProjective (Spec.map (CommRingCat.ofHom ψZ) p) := by
        rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply]
        exact congrArg (fun F => (F : Spec _ ⟶ projModelCR V₂.toProjective) p) hsqZ
      rw [hΦ, Proj.opensRange_awayι] at hx
      have hx' : Spec.map (CommRingCat.ofHom ψZ) p ∈
          zChartι V₂.toProjective ⁻¹ᵁ Proj.basicOpen (projModelGradingCR V₂.toProjective) (coord V₂.toProjective 1) := hx
      rw [Proj.awayι_preimage_basicOpen _ (coord_mem V₂.toProjective 2) one_pos (coord_mem V₂.toProjective 1) one_pos,
        isLocalizationElem_eq_yOverZ] at hx'
      have h1 : ψZ (yOverZ V₂.toProjective) ∉ p.asIdeal := hx'
      rw [hψZ, p.isPrime.pow_mem_iff_mem _ hq] at h1
      have h2 : p ∈ zChartι V₁.toProjective ⁻¹ᵁ
          Proj.basicOpen (projModelGradingCR V₁.toProjective) (coord V₁.toProjective 1) := by
        rw [Proj.awayι_preimage_basicOpen _ (coord_mem V₁.toProjective 2) one_pos (coord_mem V₁.toProjective 1) one_pos,
          isLocalizationElem_eq_yOverZ]
        exact h1
      have h3 : zChartι V₁.toProjective p ∈
          Proj.basicOpen (projModelGradingCR V₁.toProjective) (coord V₁.toProjective 1) := h2
      rwa [Proj.opensRange_awayι]
  · intro hx
    obtain ⟨p, rfl⟩ := Scheme.Hom.mem_opensRange.mp hx
    change Φ (originChartι V₁.toProjective p) ∈ (originChartι V₂.toProjective).opensRange
    rw [← Scheme.Hom.comp_apply, hsqY, Scheme.Hom.comp_apply]
    exact Scheme.Hom.mem_opensRange.mpr ⟨_, rfl⟩

theorem exists_eq_specMap_comp_originChartι {q : ℕ} (hq : 0 < q) (V₁ V₂ : WeierstrassCurve T)
    (Φ : projModelCR V₁.toProjective ⟶ projModelCR V₂.toProjective)
    (hZ : ∃ ψ : ZChartRing V₂.toProjective →+* ZChartRing V₁.toProjective,
        ψ (yOverZ V₂.toProjective) = yOverZ V₁.toProjective ^ q ∧
        zChartι V₁.toProjective ≫ Φ = Spec.map (CommRingCat.ofHom ψ) ≫ zChartι V₂.toProjective)
    (hY : ∃ ψ : OriginChartRing V₂.toProjective →+* OriginChartRing V₁.toProjective,
        originChartι V₁.toProjective ≫ Φ = Spec.map (CommRingCat.ofHom ψ) ≫ originChartι V₂.toProjective)
    {B : Type u} [CommRing B] (f : Spec (CommRingCat.of B) ⟶ projModelCR V₁.toProjective)
    (g : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of (OriginChartRing V₂.toProjective)))
    (hfg : f ≫ Φ = g ≫ originChartι V₂.toProjective) :
    ∃ χ : OriginChartRing V₁.toProjective →+* B, f = Spec.map (CommRingCat.ofHom χ) ≫ originChartι V₁.toProjective := by
  have hpre := preimage_basicOpen_Y hq V₁ V₂ Φ hZ hY
  have hrange : Set.range f ⊆ Set.range (originChartι V₁.toProjective) := by
    rintro _ ⟨s, rfl⟩
    have h1 : (f ≫ Φ) s ∈ (originChartι V₂.toProjective).opensRange := by
      rw [hfg, Scheme.Hom.comp_apply]
      exact Scheme.Hom.mem_opensRange.mpr ⟨_, rfl⟩
    have h2 : f s ∈ Φ ⁻¹ᵁ (originChartι V₂.toProjective).opensRange := by
      rw [Scheme.Hom.comp_apply] at h1
      exact h1
    rw [hpre] at h2
    exact Scheme.Hom.mem_opensRange.mp h2
  refine ⟨(Spec.preimage (IsOpenImmersion.lift (originChartι V₁.toProjective) f hrange)).hom, ?_⟩
  rw [CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]

end R4S188bFrobKerLocal

open AlgebraicGeometry CategoryTheory NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal
attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    (A : Type) [CommRing A] (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (q : ℕ) [Fact q.Prime]
    (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [Algebra A T] [CharP T q]
    (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ) (hΔq : IsUnit (W.map (frobenius T q)).Δ)
    (Φ : projModelCR W.toProjective ⟶ projModelCR (W.map (frobenius T q)).toProjective)
    (hΦ : Φ ≫ projModelStrCR (W.map (frobenius T q)).toProjective = projModelStrCR W.toProjective)
    (hZ : ∃ ψ : ZChartRing (W.map (frobenius T q)).toProjective →+* ZChartRing W.toProjective,
        ψ (xOverZ (W.map (frobenius T q)).toProjective) = xOverZ W.toProjective ^ q ∧
        ψ (yOverZ (W.map (frobenius T q)).toProjective) = yOverZ W.toProjective ^ q ∧
        zChartι W.toProjective ≫ Φ = Spec.map (CommRingCat.ofHom ψ) ≫ zChartι (W.map (frobenius T q)).toProjective)
    (hY : ∃ ψ : OriginChartRing (W.map (frobenius T q)).toProjective →+* OriginChartRing W.toProjective,
        ψ (xOverY (W.map (frobenius T q)).toProjective) = xOverY W.toProjective ^ q ∧
        ψ (zOverY (W.map (frobenius T q)).toProjective) = zOverY W.toProjective ^ q ∧
        originChartι W.toProjective ≫ Φ = Spec.map (CommRingCat.ofHom ψ) ≫ originChartι (W.map (frobenius T q)).toProjective)
    [IsFinite Φ]
    (B : Type) [CommRing B] [IsArtinianRing B] [IsLocalRing B] (ρ : T →+* B)
    (x : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (projModelStrCR W.toProjective))
    (hx : (⟨x.1 ≫ Φ, by rw [Category.assoc, hΦ]; exact x.2⟩ :
        SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (projModelStrCR (W.map (frobenius T q)).toProjective)) =
      (𝒢 T (W.map (frobenius T q)) hΔq).one _) :
    (𝒢 T W hΔ).nsmul _ q x = (𝒢 T W hΔ).one _ := by
  have hq : 0 < q := (Fact.out : q.Prime).pos
  obtain ⟨ψY, hψx, hψz, hsqY⟩ := hY
  obtain ⟨ψZ, -, hψZy, hsqZ⟩ := hZ

  obtain ⟨χ₀, hχ₀sec, hχ₀x, hχ₀z⟩ := h𝒢O T (W.map (frobenius T q)).toProjective hΔq
  set G' := 𝒢 T (W.map (frobenius T q)).toProjective hΔq with hG'
  have hone : (G'.one (Spec.map (CommRingCat.ofHom ρ))).1 =
      Spec.map (CommRingCat.ofHom ρ) ≫ Spec.map (CommRingCat.ofHom χ₀) ≫
        originChartι (W.map (frobenius T q)).toProjective := by
    have hnat := G'.one_natural (𝟙 _) (Spec.map (CommRingCat.ofHom ρ)) (Spec.map (CommRingCat.ofHom ρ))
      (Category.comp_id _)
    have h1 := congrArg Subtype.val hnat
    rw [schemeHomOverComp_coe] at h1
    rw [← h1]
    exact congrArg (fun F => Spec.map (CommRingCat.ofHom ρ) ≫ F) hχ₀sec

  have hxΦ : x.1 ≫ Φ = Spec.map (CommRingCat.ofHom (ρ.comp χ₀)) ≫
      originChartι (W.map (frobenius T q)).toProjective := by
    have h1 := congrArg Subtype.val hx
    dsimp only at h1
    rw [h1, hone, CommRingCat.ofHom_comp, Spec.map_comp_assoc]

  obtain ⟨χ, hxχ⟩ := R4S188bFrobKerLocal.exists_eq_specMap_comp_originChartι hq W (W.map (frobenius T q)) Φ
    ⟨ψZ, hψZy, hsqZ⟩ ⟨ψY, hsqY⟩ x.1 (Spec.map (CommRingCat.ofHom (ρ.comp χ₀))) hxΦ

  have hcomp : χ.comp ψY = ρ.comp χ₀ := by
    have h1 : Spec.map (CommRingCat.ofHom χ) ≫ Spec.map (CommRingCat.ofHom ψY) ≫
        originChartι (W.map (frobenius T q)).toProjective =
        Spec.map (CommRingCat.ofHom (ρ.comp χ₀)) ≫ originChartι (W.map (frobenius T q)).toProjective := by
      rw [← hxΦ, hxχ, Category.assoc, hsqY]
    rw [← Category.assoc, cancel_mono, ← Spec.map_comp, ← CommRingCat.ofHom_comp] at h1
    have h2 := congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
    simpa only [CommRingCat.hom_ofHom] using h2
  have hXq : (χ (xOverY W.toProjective)) ^ q = 0 := by
    have h := congrArg (fun φ : OriginChartRing (W.map (frobenius T q)).toProjective →+* B =>
      φ (xOverY (W.map (frobenius T q)).toProjective)) hcomp
    simp only [RingHom.comp_apply, hψx, map_pow, hχ₀x, map_zero] at h
    exact h
  have hZq : (χ (zOverY W.toProjective)) ^ q = 0 := by
    have h := congrArg (fun φ : OriginChartRing (W.map (frobenius T q)).toProjective →+* B =>
      φ (zOverY (W.map (frobenius T q)).toProjective)) hcomp
    simp only [RingHom.comp_apply, hψz, map_pow, hχ₀z, map_zero] at h
    exact h

  exact WeierstrassCurve.DrinfeldGlobal.nsmul_eq_one_of_comp_originChartIota_of_pow_eq_zero_of_isAdicComplete
    A 𝒢 h𝒢 h𝒢O q T W hΔ B ρ x χ hxχ hXq hZq

end S_WeierstrassCurve_DrinfeldGlobal_nsmul_eq_one_of_comp_eq_one_of_zChart_pow_originChart_pow_of_isArtinianRing
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_nsmul_eq_one_of_comp_eq_one_of_zChart_pow_originChart_pow_of_isArtinianRing (solution)
