-- Prove2me | solution 1 for WeierstrassProjModel.coeff_laurent_zChart_of_iso_of_kwZeroSect_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/2bc1cb4c-7cf5-591c-b499-571ffb54dca5

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
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_ringHom_originChartRing_ext
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_originChart_rel_unique_of_mem_maximalIdeal
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_ringHom_originChartRing_powerSeries
import Theorems.Thm_WeierstrassProjModel_exists_zChartAway_equiv_coordinateRing
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_coeff_laurent_zChart_of_iso_of_kwZeroSect_comp_eq

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

set_option linter.unusedVariables false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal HomogeneousLocalization HomogeneousIdealQuotientGrading

namespace OverlapAux

section Away

variable {T : Type} [CommRing T] (V : WeierstrassCurve.Projective T)

noncomputable abbrev toOverlapY : OriginChartRing V →+* Away (projModelGradingCR V) (coord V 1 * coord V 2) :=
  awayMap (projModelGradingCR V) (coord_mem V 2) (rfl : coord V 1 * coord V 2 = coord V 1 * coord V 2)

noncomputable abbrev toOverlapZ : ZChartRing V →+* Away (projModelGradingCR V) (coord V 1 * coord V 2) :=
  awayMap (projModelGradingCR V) (coord_mem V 1)
    ((rfl : coord V 1 * coord V 2 = coord V 1 * coord V 2).trans (mul_comm _ _))

theorem overlap_identities :
    toOverlapZ V (xOverZ V) * toOverlapY V (zOverY V) = toOverlapY V (xOverY V) ∧
    toOverlapZ V (yOverZ V) * toOverlapY V (zOverY V) = 1 := by
  constructor
  · unfold toOverlapZ toOverlapY xOverZ zOverY xOverY
    rw [awayMap_mk, awayMap_mk, awayMap_mk]
    refine HomogeneousLocalization.val_injective _ ?_
    simp only [HomogeneousLocalization.val_mul, Away.val_mk, Localization.mk_mul]
    rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    refine ⟨1, ?_⟩
    simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul, pow_one]
    ring
  · unfold toOverlapZ toOverlapY yOverZ zOverY
    rw [awayMap_mk, awayMap_mk]
    refine HomogeneousLocalization.val_injective _ ?_
    simp only [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_one, Away.val_mk, Localization.mk_mul]
    rw [← Localization.mk_one, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    refine ⟨1, ?_⟩
    simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul, pow_one, mul_one]
    ring

theorem exists_overlap_hom_of_specMap_comp_eq {S : Type} [CommRing S]
    (a : OriginChartRing V →+* S) (b : ZChartRing V →+* S)
    (h : Spec.map (CommRingCat.ofHom a) ≫ originChartι V = Spec.map (CommRingCat.ofHom b) ≫ zChartι V) :
    ∃ c : Away (projModelGradingCR V) (coord V 1 * coord V 2) →+* S,
      c.comp (toOverlapY V) = a ∧ c.comp (toOverlapZ V) = b := by
  let P := pullback.lift (Spec.map (CommRingCat.ofHom a)) (Spec.map (CommRingCat.ofHom b)) h
  let e := Proj.pullbackAwayιIso (projModelGradingCR V) (coord_mem V 1) one_pos (coord_mem V 2) one_pos
    (rfl : coord V 1 * coord V 2 = coord V 1 * coord V 2)
  obtain ⟨c, hc⟩ := Spec.map_surjective (P ≫ e.hom)
  have ha : Spec.map c ≫ Spec.map (CommRingCat.ofHom (toOverlapY V)) = Spec.map (CommRingCat.ofHom a) := by
    rw [hc, Category.assoc]
    erw [Proj.pullbackAwayιIso_hom_SpecMap_awayMap_left]
    exact pullback.lift_fst _ _ _
  have hb : Spec.map c ≫ Spec.map (CommRingCat.ofHom (toOverlapZ V)) = Spec.map (CommRingCat.ofHom b) := by
    rw [hc, Category.assoc]
    erw [Proj.pullbackAwayιIso_hom_SpecMap_awayMap_right]
    exact pullback.lift_snd _ _ _
  rw [← Spec.map_comp] at ha hb
  have ha' := Spec.map_injective ha
  have hb' := Spec.map_injective hb
  refine ⟨c.hom, ?_, ?_⟩
  · ext r; exact congrArg (fun φ => φ.hom r) ha'
  · ext r; exact congrArg (fun φ => φ.hom r) hb'

theorem zChart_mul_originChart_of_specMap_comp_eq {S : Type} [CommRing S]
    (a : OriginChartRing V →+* S) (b : ZChartRing V →+* S)
    (h : Spec.map (CommRingCat.ofHom a) ≫ originChartι V = Spec.map (CommRingCat.ofHom b) ≫ zChartι V) :
    b (xOverZ V) * a (zOverY V) = a (xOverY V) ∧ b (yOverZ V) * a (zOverY V) = 1 := by
  obtain ⟨c, hca, hcb⟩ := exists_overlap_hom_of_specMap_comp_eq V a b h
  obtain ⟨h1, h2⟩ := overlap_identities V
  subst hca hcb
  simp only [RingHom.comp_apply]
  refine ⟨?_, ?_⟩
  · calc c (toOverlapZ V (xOverZ V)) * c (toOverlapY V (zOverY V))
        = c (toOverlapZ V (xOverZ V) * toOverlapY V (zOverY V)) := (map_mul c _ _).symm
      _ = c (toOverlapY V (xOverY V)) := congrArg c h1
  · calc c (toOverlapZ V (yOverZ V)) * c (toOverlapY V (zOverY V))
        = c (toOverlapZ V (yOverZ V) * toOverlapY V (zOverY V)) := (map_mul c _ _).symm
      _ = c 1 := congrArg c h2
      _ = 1 := map_one c

end Away

end OverlapAux

namespace OverlapAux

section Str

variable {T : Type} [CommRing T] (V : WeierstrassCurve.Projective T)

noncomputable def zStr : T →+* ZChartRing V :=
  (fromZeroRingHom (projModelGradingCR V) _).comp (algebraMap T (projModelGradingCR V 0))

noncomputable def oStr : T →+* OriginChartRing V :=
  (fromZeroRingHom (projModelGradingCR V) _).comp (algebraMap T (projModelGradingCR V 0))

theorem zChartι_comp_projModelStrCR : zChartι V ≫ projModelStrCR V = Spec.map (CommRingCat.ofHom (zStr V)) := by
  rw [projModelStrCR, ← Category.assoc]
  erw [Proj.awayι_toSpecZero]
  rw [← Spec.map_comp]
  rfl

theorem originChartι_comp_projModelStrCR :
    originChartι V ≫ projModelStrCR V = Spec.map (CommRingCat.ofHom (oStr V)) := by
  rw [projModelStrCR, ← Category.assoc]
  erw [Proj.awayι_toSpecZero]
  rw [← Spec.map_comp]
  rfl

theorem zChart_ringHom_ext {B : Type} [CommRing B]
    (g₁ g₂ : ZChartRing V →+* B) (h0 : g₁.comp (zStr V) = g₂.comp (zStr V))
    (hx : g₁ (xOverZ V) = g₂ (xOverZ V)) (hy : g₁ (yOverZ V) = g₂ (yOverZ V)) : g₁ = g₂ := by
  classical
  obtain ⟨f, hbij, hcomp, hmk⟩ := WeierstrassProjModel.exists_zChartAway_equiv_coordinateRing V
  let e := RingEquiv.ofBijective f hbij
  have hx' : e.symm (Ideal.Quotient.mk _ (Polynomial.C Polynomial.X)) = xOverZ V := by
    apply e.injective
    rw [RingEquiv.apply_symm_apply]
    have := hmk 1 (MvPolynomial.X 0)
      ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (by simpa using MvPolynomial.isHomogeneous_X T 0))
    simp only [MvPolynomial.aeval_X, Matrix.cons_val_zero] at this
    exact this.symm
  have hy' : e.symm (Ideal.Quotient.mk _ Polynomial.X) = yOverZ V := by
    apply e.injective
    rw [RingEquiv.apply_symm_apply]
    have := hmk 1 (MvPolynomial.X 1)
      ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (by simpa using MvPolynomial.isHomogeneous_X T 1))
    simp only [MvPolynomial.aeval_X, Matrix.cons_val_one, Matrix.head_cons] at this
    exact this.symm
  have hr : ∀ r : T, e.symm (Ideal.Quotient.mk _ (Polynomial.C (Polynomial.C r))) = zStr V r := by
    intro r
    apply e.injective
    rw [RingEquiv.apply_symm_apply]
    exact (RingHom.congr_fun hcomp r).symm
  suffices h : (g₁.comp e.symm.toRingHom).comp (Ideal.Quotient.mk _) =
      (g₂.comp e.symm.toRingHom).comp (Ideal.Quotient.mk _) by
    have h' : g₁.comp e.symm.toRingHom = g₂.comp e.symm.toRingHom := Ideal.Quotient.ringHom_ext h
    ext x
    have := RingHom.congr_fun h' (e x)
    rwa [RingHom.comp_apply, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      RingEquiv.symm_apply_apply] at this
  apply Polynomial.ringHom_ext'
  · apply Polynomial.ringHom_ext'
    · ext r
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hr]
      exact RingHom.congr_fun h0 r
    · simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hx']
      exact hx
  · simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hy']
    exact hy

end Str

section Laurent

variable {T : Type} [CommRing T] (V : WeierstrassCurve.Projective T)

theorem isLocalizationElem_eq_zOverY :
    Away.isLocalizationElem (coord_mem V 1) (coord_mem V 2) = zOverY V := by
  unfold Away.isLocalizationElem zOverY
  congr 1
  exact pow_one _

theorem specMap_comp_zChartι_eq_of_laurent
    (Φ : OriginChartRing V →+* PowerSeries T)
    (hΦc : ∀ t : T, Φ (fromZeroRingHom (projModelGradingCR V) _ (algebraMap T (projModelGradingCR V 0) t)) =
      PowerSeries.C t)
    (lam : ZChartRing V →+* LaurentSeries T)
    (hlamc : ∀ t : T, lam (fromZeroRingHom (projModelGradingCR V) _ (algebraMap T (projModelGradingCR V 0) t)) =
      HahnSeries.C t)
    (hlamx : lam (xOverZ V) * HahnSeries.ofPowerSeries ℤ T (Φ (zOverY V)) =
      HahnSeries.ofPowerSeries ℤ T (Φ (xOverY V)))
    (hlamy : lam (yOverZ V) * HahnSeries.ofPowerSeries ℤ T (Φ (zOverY V)) = 1)
    (hunit : IsUnit (HahnSeries.ofPowerSeries ℤ T (Φ (zOverY V)))) :
    Spec.map (CommRingCat.ofHom lam) ≫ zChartι V =
      Spec.map (CommRingCat.ofHom ((HahnSeries.ofPowerSeries ℤ T).comp Φ)) ≫ originChartι V := by
  classical
  set a : OriginChartRing V →+* LaurentSeries T := (HahnSeries.ofPowerSeries ℤ T).comp Φ with ha

  have hrange : Set.range (Spec.map (CommRingCat.ofHom a) ≫ originChartι V).base ⊆ Set.range (zChartι V).base := by
    rintro _ ⟨p, rfl⟩
    have hmem : (Spec.map (CommRingCat.ofHom a)).base p ∈
        originChartι V ⁻¹ᵁ Proj.basicOpen (projModelGradingCR V) (coord V 2) := by
      rw [Proj.awayι_preimage_basicOpen _ _ _ (coord_mem V 2) one_pos, isLocalizationElem_eq_zOverY]
      show a (zOverY V) ∉ p.asIdeal
      exact fun h => p.2.ne_top (Ideal.eq_top_of_isUnit_mem _ h hunit)
    have : (originChartι V).base ((Spec.map (CommRingCat.ofHom a)).base p) ∈ (zChartι V).opensRange := by
      rw [Proj.opensRange_awayι]; exact hmem
    obtain ⟨y, hy⟩ := Scheme.Hom.mem_opensRange.mp this
    exact ⟨y, by rw [Scheme.Hom.comp_base]; exact hy⟩

  obtain ⟨μ, hμ⟩ := Spec.map_surjective
    (IsOpenImmersion.lift (zChartι V) (Spec.map (CommRingCat.ofHom a) ≫ originChartι V) hrange)
  have hfac : Spec.map μ ≫ zChartι V = Spec.map (CommRingCat.ofHom a) ≫ originChartι V := by
    rw [hμ]; exact IsOpenImmersion.lift_fac _ _ _

  have hμlam : μ.hom = lam := by
    apply zChart_ringHom_ext V
    ·
      have h1 := congrArg (· ≫ projModelStrCR V) hfac
      simp only [Category.assoc, zChartι_comp_projModelStrCR, originChartι_comp_projModelStrCR, ← Spec.map_comp] at h1
      have h2 := Spec.map_injective h1
      refine RingHom.ext fun t => ?_
      have h3 := congrArg (fun φ => φ.hom t) h2
      simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at h3
      rw [RingHom.comp_apply, RingHom.comp_apply, h3]
      have e1 : a (oStr V t) = HahnSeries.C t := by
        show HahnSeries.ofPowerSeries ℤ T
          (Φ (fromZeroRingHom (projModelGradingCR V) _ (algebraMap T (projModelGradingCR V 0) t))) = _
        rw [hΦc, HahnSeries.ofPowerSeries_C]
      have e2 : lam (zStr V t) = HahnSeries.C t := hlamc t
      rw [e1, e2]
    · obtain ⟨e1, -⟩ := zChart_mul_originChart_of_specMap_comp_eq V a μ.hom hfac.symm
      have : μ.hom (xOverZ V) * a (zOverY V) = lam (xOverZ V) * a (zOverY V) := by rw [e1, ha]; exact hlamx.symm
      exact hunit.mul_right_cancel this
    · obtain ⟨-, e2⟩ := zChart_mul_originChart_of_specMap_comp_eq V a μ.hom hfac.symm
      have : μ.hom (yOverZ V) * a (zOverY V) = lam (yOverZ V) * a (zOverY V) := by rw [e2, ha]; exact hlamy.symm
      exact hunit.mul_right_cancel this
  have : CommRingCat.ofHom lam = μ := by rw [← hμlam]; rfl
  rw [this, hfac]

end Laurent

end OverlapAux

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

section FormalPoint

variable {T : Type} [CommRing T] [IsLocalRing T] (W W' : WeierstrassCurve T)

omit [IsLocalRing T] in
theorem originChartι_comp_projModelStrCR (V : WeierstrassCurve T) :
    originChartι V.toProjective ≫ projModelStrCR V.toProjective = Spec.map (CommRingCat.ofHom (cY V)) := by
  simp only [projModelStrCR]
  rw [← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem exists_formalChart_of_iso
    (Ψ : projModelCR W.toProjective ≅ projModelCR W'.toProjective)
    (hΨ : Ψ.hom ≫ projModelStrCR W'.toProjective = projModelStrCR W.toProjective)
    (hΨO : (kwZeroSect T W).1 ≫ Ψ.hom = (kwZeroSect T W').1)
    (Φ : OriginChartRing W.toProjective →+* PowerSeries T)
    (hΦc : ∀ t : T, Φ (cY W t) = PowerSeries.C t)
    (hΦx : Φ (xOverY W.toProjective) = - PowerSeries.X) (hΦz : Φ (zOverY W.toProjective) = - W.formalW) :
    ∃ χ' : OriginChartRing W'.toProjective →+* PowerSeries T,
      (∀ t : T, χ' (cY W' t) = PowerSeries.C t) ∧
      PowerSeries.constantCoeff (χ' (xOverY W'.toProjective)) = 0 ∧
      PowerSeries.constantCoeff (χ' (zOverY W'.toProjective)) = 0 ∧
      Spec.map (CommRingCat.ofHom χ') ≫ originChartι W'.toProjective =
        Spec.map (CommRingCat.ofHom Φ) ≫ originChartι W.toProjective ≫ Ψ.hom := by
  haveI : IsLocalRing (PowerSeries T) := inferInstanceAs (IsLocalRing (MvPowerSeries Unit T))
  obtain ⟨hO', hχx', hχz'⟩ := WeierstrassProjModel.isOriginChartSection_kwZeroSect_kwYChartEval W'.toProjective
  have hO'' : (kwZeroSect T W').1 =
      Spec.map (CommRingCat.ofHom (kwYChartEval T W')) ≫ originChartι W'.toProjective := hO'
  obtain ⟨hO, hχx, hχz⟩ := WeierstrassProjModel.isOriginChartSection_kwZeroSect_kwYChartEval W.toProjective
  have hOW : (kwZeroSect T W).1 =
      Spec.map (CommRingCat.ofHom (kwYChartEval T W)) ≫ originChartι W.toProjective := hO
  let P : Spec (CommRingCat.of (PowerSeries T)) ⟶ projModelCR W'.toProjective :=
    Spec.map (CommRingCat.ofHom Φ) ≫ originChartι W.toProjective ≫ Ψ.hom

  have hred : (PowerSeries.constantCoeff (R := T)).comp Φ = kwYChartEval T W := by
    apply WeierstrassCurve.DrinfeldGlobal.ringHom_originChartRing_ext W
    · intro t
      have h := hΦc t
      have h2 := RingHom.congr_fun (kwYChartEval_section T W) t
      simp only [RingHom.comp_apply, RingHom.id_apply] at h h2
      rw [RingHom.comp_apply, h, PowerSeries.constantCoeff_C]
      exact h2.symm
    · rw [RingHom.comp_apply, hΦx, map_neg, PowerSeries.constantCoeff_X, neg_zero]; exact hχx.symm
    · rw [RingHom.comp_apply, hΦz, map_neg, WeierstrassCurve.constantCoeff_formalW, neg_zero]; exact hχz.symm

  have hrange : Set.range P ⊆ Set.range (originChartι W'.toProjective) := by

    let c := IsLocalRing.closedPoint (PowerSeries T)
    have hc : P c ∈ Set.range (originChartι W'.toProjective) := by

      have hcc : Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := T))) (IsLocalRing.closedPoint T) = c := by
        apply PrimeSpectrum.ext
        change Ideal.comap (PowerSeries.constantCoeff (R := T)) (IsLocalRing.maximalIdeal T) =
          IsLocalRing.maximalIdeal (PowerSeries T)
        haveI : IsLocalHom (PowerSeries.constantCoeff (R := T)) :=
          ⟨fun a ha => (PowerSeries.isUnit_iff_constantCoeff).mpr ha⟩
        exact congrArg PrimeSpectrum.asIdeal (IsLocalRing.comap_closedPoint (PowerSeries.constantCoeff (R := T)))
      have h1 : P c = ((kwZeroSect T W).1 ≫ Ψ.hom) (IsLocalRing.closedPoint T) := by
        rw [← hcc, hOW]
        simp only [P, ← Scheme.Hom.comp_apply, Category.assoc, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, hred]
      rw [h1, hΨO, hO'', Scheme.Hom.comp_apply]
      exact ⟨_, rfl⟩
    rintro _ ⟨z, rfl⟩
    have hz : z ⤳ c := (PrimeSpectrum.le_iff_specializes z c).mp (IsLocalRing.le_maximalIdeal z.isPrime.ne_top)
    have hPz : P z ⤳ P c := hz.map P.continuous
    have hopen : IsOpen (Set.range (originChartι W'.toProjective)) := (originChartι W'.toProjective).isOpenEmbedding.isOpen_range
    exact hPz.mem_open hopen hc

  let Q := IsOpenImmersion.lift (originChartι W'.toProjective) P hrange
  have hQ : Q ≫ originChartι W'.toProjective = P := IsOpenImmersion.lift_fac _ _ hrange
  obtain ⟨φ, hφ⟩ := Spec.map_surjective Q

  have hmod : Spec.map (CommRingCat.ofHom ((PowerSeries.constantCoeff (R := T)).comp φ.hom)) ≫
      originChartι W'.toProjective = (kwZeroSect T W').1 := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, show CommRingCat.ofHom φ.hom = φ from rfl, hφ, hQ]
    simp only [P, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hred]
    rw [← hOW, hΨO]
  rw [hO''] at hmod
  have hmod' : (PowerSeries.constantCoeff (R := T)).comp φ.hom = kwYChartEval T W' := by
    have := Spec.map_injective ((cancel_mono (originChartι W'.toProjective)).mp hmod)
    exact congrArg CommRingCat.Hom.hom this
  refine ⟨φ.hom, ?_, by rw [← RingHom.comp_apply, hmod']; exact hχx',
    by rw [← RingHom.comp_apply, hmod']; exact hχz', by rw [show CommRingCat.ofHom φ.hom = φ from rfl, hφ, hQ]⟩
  ·
    have h2 : Spec.map φ ≫ Spec.map (CommRingCat.ofHom (cY W')) = Spec.map (CommRingCat.ofHom (Φ.comp (cY W))) := by
      rw [← originChartι_comp_projModelStrCR W', hφ, ← Category.assoc, hQ]
      simp only [P, Category.assoc, hΨ]
      rw [originChartι_comp_projModelStrCR W, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have h3 : CommRingCat.ofHom (cY W') ≫ φ = CommRingCat.ofHom (Φ.comp (cY W)) :=
      Spec.map_injective (by rw [Spec.map_comp]; exact h2)
    intro t
    have := congrArg (fun f : CommRingCat.of T ⟶ CommRingCat.of (PowerSeries T) => f.hom t) h3
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply] at this
    exact this.trans (hΦc t)

end FormalPoint

section Subst

variable {T : Type} [CommRing T] [IsLocalRing T]

theorem formalChart_zOverY_eq (V : WeierstrassCurve T)
    (χ : OriginChartRing V.toProjective →+* PowerSeries T)
    (hc : ∀ t : T, χ (cY V t) = PowerSeries.C t)
    (hx0 : PowerSeries.constantCoeff (χ (xOverY V.toProjective)) = 0)
    (hz0 : PowerSeries.constantCoeff (χ (zOverY V.toProjective)) = 0)
    (Φ : OriginChartRing V.toProjective →+* PowerSeries T)
    (hΦc : ∀ t : T, Φ (cY V t) = PowerSeries.C t)
    (hΦx : Φ (xOverY V.toProjective) = - PowerSeries.X) (hΦz : Φ (zOverY V.toProjective) = - V.formalW) :
    χ (zOverY V.toProjective) = - PowerSeries.subst (- χ (xOverY V.toProjective)) V.formalW := by
  haveI : IsLocalRing (PowerSeries T) := inferInstanceAs (IsLocalRing (MvPowerSeries Unit T))
  set α : PowerSeries T := - χ (xOverY V.toProjective) with hα
  have hα0 : PowerSeries.constantCoeff α = 0 := by rw [hα, map_neg, hx0, neg_zero]
  have hαs : PowerSeries.HasSubst α := PowerSeries.HasSubst.of_constantCoeff_zero' hα0

  let ρ : OriginChartRing V.toProjective →+* PowerSeries T := (PowerSeries.substAlgHom (R := T) hαs).toRingHom.comp Φ
  have hρc : ∀ t : T, ρ (cY V t) = PowerSeries.C t := by
    intro t
    show PowerSeries.substAlgHom (R := T) hαs (Φ (cY V t)) = _
    rw [hΦc, PowerSeries.coe_substAlgHom, PowerSeries.subst_C]; rfl
  have hρx : ρ (xOverY V.toProjective) = χ (xOverY V.toProjective) := by
    show PowerSeries.substAlgHom (R := T) hαs (Φ (xOverY V.toProjective)) = _
    rw [hΦx, map_neg, PowerSeries.coe_substAlgHom, PowerSeries.subst_X hαs, hα, neg_neg]
  have hρz : ρ (zOverY V.toProjective) = - PowerSeries.subst α V.formalW := by
    show PowerSeries.substAlgHom (R := T) hαs (Φ (zOverY V.toProjective)) = _
    rw [hΦz, map_neg, PowerSeries.coe_substAlgHom]

  have mem_of_cc : ∀ f : PowerSeries T, PowerSeries.constantCoeff f = 0 → f ∈ IsLocalRing.maximalIdeal (PowerSeries T) := by
    intro f hf
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff, hf]
    exact not_isUnit_zero
  have h1 := WeierstrassCurve.DrinfeldGlobal.originChart_rel V χ
    (fun t => by change χ ((cY V) t) = _; rw [hc t, PowerSeries.algebraMap_eq])
  have h2 := WeierstrassCurve.DrinfeldGlobal.originChart_rel V ρ
    (fun t => by change ρ ((cY V) t) = _; rw [hρc t, PowerSeries.algebraMap_eq])
  rw [hρx, hρz] at h2
  rw [← hρz] at h2 ⊢
  refine WeierstrassCurve.DrinfeldGlobal.originChart_rel_unique_of_mem_maximalIdeal _ _ _ _ _ _ _ _
    (mem_of_cc _ hx0) (mem_of_cc _ hz0) (mem_of_cc _ ?_) h1 h2
  rw [hρz, map_neg, neg_eq_zero]
  exact PowerSeries.constantCoeff_subst_eq_zero hα0 _ V.constantCoeff_formalW

theorem formalChart_eq_subst_comp (V : WeierstrassCurve T)
    (χ : OriginChartRing V.toProjective →+* PowerSeries T)
    (hc : ∀ t : T, χ (cY V t) = PowerSeries.C t)
    (hx0 : PowerSeries.constantCoeff (χ (xOverY V.toProjective)) = 0)
    (hz0 : PowerSeries.constantCoeff (χ (zOverY V.toProjective)) = 0)
    (Φ : OriginChartRing V.toProjective →+* PowerSeries T)
    (hΦc : ∀ t : T, Φ (cY V t) = PowerSeries.C t)
    (hΦx : Φ (xOverY V.toProjective) = - PowerSeries.X) (hΦz : Φ (zOverY V.toProjective) = - V.formalW)
    (hαs : PowerSeries.HasSubst (- χ (xOverY V.toProjective))) :
    χ = (PowerSeries.substAlgHom (R := T) hαs).toRingHom.comp Φ := by
  apply WeierstrassCurve.DrinfeldGlobal.ringHom_originChartRing_ext V
  · intro t
    change χ (cY V t) = PowerSeries.substAlgHom (R := T) hαs (Φ (cY V t))
    rw [hc, hΦc, PowerSeries.coe_substAlgHom, PowerSeries.subst_C]; rfl
  · change _ = PowerSeries.substAlgHom (R := T) hαs (Φ (xOverY V.toProjective))
    rw [hΦx, map_neg, PowerSeries.coe_substAlgHom, PowerSeries.subst_X hαs, neg_neg]
  · change _ = PowerSeries.substAlgHom (R := T) hαs (Φ (zOverY V.toProjective))
    rw [hΦz, map_neg, PowerSeries.coe_substAlgHom, formalChart_zOverY_eq V χ hc hx0 hz0 Φ hΦc hΦx hΦz]

end Subst

section UnitCoeff

variable {T : Type} [CommRing T] [IsLocalRing T] (W W' : WeierstrassCurve T)

theorem isUnit_coeff_one_formalChart
    (Ψ : projModelCR W.toProjective ≅ projModelCR W'.toProjective)
    (hΨ : Ψ.hom ≫ projModelStrCR W'.toProjective = projModelStrCR W.toProjective)
    (hΨO : (kwZeroSect T W).1 ≫ Ψ.hom = (kwZeroSect T W').1)
    (Φ : OriginChartRing W.toProjective →+* PowerSeries T)
    (hΦc : ∀ t : T, Φ (cY W t) = PowerSeries.C t)
    (hΦx : Φ (xOverY W.toProjective) = - PowerSeries.X) (hΦz : Φ (zOverY W.toProjective) = - W.formalW)
    (Φ' : OriginChartRing W'.toProjective →+* PowerSeries T)
    (hΦc' : ∀ t : T, Φ' (cY W' t) = PowerSeries.C t)
    (hΦx' : Φ' (xOverY W'.toProjective) = - PowerSeries.X) (hΦz' : Φ' (zOverY W'.toProjective) = - W'.formalW)
    (χ' : OriginChartRing W'.toProjective →+* PowerSeries T)
    (hc' : ∀ t : T, χ' (cY W' t) = PowerSeries.C t)
    (hx0 : PowerSeries.constantCoeff (χ' (xOverY W'.toProjective)) = 0)
    (hz0 : PowerSeries.constantCoeff (χ' (zOverY W'.toProjective)) = 0)
    (hχ' : Spec.map (CommRingCat.ofHom χ') ≫ originChartι W'.toProjective =
        Spec.map (CommRingCat.ofHom Φ) ≫ originChartι W.toProjective ≫ Ψ.hom) :
    IsUnit (PowerSeries.coeff 1 (χ' (xOverY W'.toProjective))) := by

  have hΨ' : Ψ.inv ≫ projModelStrCR W.toProjective = projModelStrCR W'.toProjective := by
    rw [← hΨ, Iso.inv_hom_id_assoc]
  have hΨO' : (kwZeroSect T W').1 ≫ Ψ.inv = (kwZeroSect T W).1 := by
    rw [← hΨO, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  obtain ⟨χ'', hc'', hx0'', hz0'', hχ''⟩ := exists_formalChart_of_iso W' W Ψ.symm hΨ' hΨO' Φ' hΦc' hΦx' hΦz'
  simp only [Iso.symm_hom] at hχ''

  set α : PowerSeries T := - χ' (xOverY W'.toProjective) with hα
  set β : PowerSeries T := - χ'' (xOverY W.toProjective) with hβ
  have hα0 : PowerSeries.constantCoeff α = 0 := by rw [hα, map_neg, hx0, neg_zero]
  have hβ0 : PowerSeries.constantCoeff β = 0 := by rw [hβ, map_neg, hx0'', neg_zero]
  have hαs : PowerSeries.HasSubst α := PowerSeries.HasSubst.of_constantCoeff_zero' hα0
  have hβs : PowerSeries.HasSubst β := PowerSeries.HasSubst.of_constantCoeff_zero' hβ0
  have e1 := formalChart_eq_subst_comp W' χ' hc' hx0 hz0 Φ' hΦc' hΦx' hΦz' hαs
  have e2 := formalChart_eq_subst_comp W χ'' hc'' hx0'' hz0'' Φ hΦc hΦx hΦz hβs

  have key : Spec.map (CommRingCat.ofHom Φ) ≫ originChartι W.toProjective =
      Spec.map (CommRingCat.ofHom (PowerSeries.substAlgHom (R := T) hαs).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (PowerSeries.substAlgHom (R := T) hβs).toRingHom) ≫
          Spec.map (CommRingCat.ofHom Φ) ≫ originChartι W.toProjective := by
    have h1 : Spec.map (CommRingCat.ofHom Φ) ≫ originChartι W.toProjective =
        Spec.map (CommRingCat.ofHom χ') ≫ originChartι W'.toProjective ≫ Ψ.inv := by
      rw [← Category.assoc, hχ', Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    have h2 : Spec.map (CommRingCat.ofHom χ') =
        Spec.map (CommRingCat.ofHom (PowerSeries.substAlgHom (R := T) hαs).toRingHom) ≫ Spec.map (CommRingCat.ofHom Φ') := by
      rw [e1, CommRingCat.ofHom_comp, Spec.map_comp]
    have h3 : Spec.map (CommRingCat.ofHom χ'') =
        Spec.map (CommRingCat.ofHom (PowerSeries.substAlgHom (R := T) hβs).toRingHom) ≫ Spec.map (CommRingCat.ofHom Φ) := by
      rw [e2, CommRingCat.ofHom_comp, Spec.map_comp]
    calc Spec.map (CommRingCat.ofHom Φ) ≫ originChartι W.toProjective
        = Spec.map (CommRingCat.ofHom χ') ≫ originChartι W'.toProjective ≫ Ψ.inv := h1
      _ = Spec.map (CommRingCat.ofHom (PowerSeries.substAlgHom (R := T) hαs).toRingHom) ≫
            (Spec.map (CommRingCat.ofHom Φ') ≫ originChartι W'.toProjective ≫ Ψ.inv) := by
          rw [h2, Category.assoc]
      _ = Spec.map (CommRingCat.ofHom (PowerSeries.substAlgHom (R := T) hαs).toRingHom) ≫
            (Spec.map (CommRingCat.ofHom χ'') ≫ originChartι W.toProjective) := by rw [hχ'']
      _ = _ := by rw [h3, Category.assoc]
  have key2 : CommRingCat.ofHom Φ =
      CommRingCat.ofHom Φ ≫ CommRingCat.ofHom (PowerSeries.substAlgHom (R := T) hβs).toRingHom ≫
        CommRingCat.ofHom (PowerSeries.substAlgHom (R := T) hαs).toRingHom := by
    apply Spec.map_injective
    apply (cancel_mono (originChartι W.toProjective)).mp
    simpa only [Spec.map_comp, Category.assoc] using key

  have hsub : PowerSeries.subst α β = PowerSeries.X := by
    have := congrArg (fun f : CommRingCat.of (OriginChartRing W.toProjective) ⟶ CommRingCat.of (PowerSeries T) =>
      f.hom (xOverY W.toProjective)) key2
    simp only [CommRingCat.hom_ofHom, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at this
    rw [hΦx] at this
    change -PowerSeries.X = PowerSeries.substAlgHom (R := T) hαs (PowerSeries.substAlgHom (R := T) hβs (-PowerSeries.X)) at this
    rw [map_neg, map_neg, PowerSeries.coe_substAlgHom hβs, PowerSeries.subst_X hβs,
      PowerSeries.coe_substAlgHom hαs] at this
    exact (neg_inj.mp this).symm

  obtain ⟨a, ha⟩ := PowerSeries.X_dvd_iff.mpr hα0
  obtain ⟨b, hb⟩ := PowerSeries.X_dvd_iff.mpr hβ0
  have hprod : PowerSeries.X * (a * PowerSeries.subst α b) = PowerSeries.X * 1 := by
    calc PowerSeries.X * (a * PowerSeries.subst α b) = (PowerSeries.X * a) * PowerSeries.subst α b := by ring
      _ = PowerSeries.subst α (PowerSeries.X : PowerSeries T) * PowerSeries.subst α b := by rw [← ha, PowerSeries.subst_X hαs]
      _ = PowerSeries.subst α β := by rw [← PowerSeries.subst_mul hαs, ← hb]
      _ = PowerSeries.X * 1 := by rw [hsub, mul_one]
  have hone : a * PowerSeries.subst α b = 1 := by
    ext n
    have := congrArg (PowerSeries.coeff (n + 1)) hprod
    rwa [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_succ_X_mul] at this
  have hau : IsUnit a := ⟨⟨a, PowerSeries.subst α b, hone, (mul_comm _ _).trans hone⟩, rfl⟩
  have hcoeff : PowerSeries.coeff 1 (χ' (xOverY W'.toProjective)) = - PowerSeries.constantCoeff a := by
    have : χ' (xOverY W'.toProjective) = - (PowerSeries.X * a) := by rw [← ha, hα, neg_neg]
    rw [this, map_neg, show (1 : ℕ) = 0 + 1 from rfl, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_zero_eq_constantCoeff_apply]
  rw [hcoeff]
  exact ((PowerSeries.isUnit_iff_constantCoeff).mp hau).neg

end UnitCoeff

section LaurentCore

variable {T : Type} [CommRing T]

local notation "ofPS" => HahnSeries.ofPowerSeries ℤ T

theorem single_one_mul_single_neg_one' :
    (HahnSeries.single (1 : ℤ) (1 : T) : LaurentSeries T) * HahnSeries.single (-1 : ℤ) (1 : T) = 1 := by
  rw [HahnSeries.single_mul_single, mul_one]; norm_num

theorem coeff_ofPS_mul_single' (g : PowerSeries T) (k n : ℤ) :
    (ofPS g * HahnSeries.single k (1 : T)).coeff n =
      if n - k < 0 then 0 else PowerSeries.coeff (n - k).natAbs g := by
  rw [HahnSeries.coeff_mul_single, mul_one]
  exact PowerSeries.coeff_coe g (n - k)

theorem coeff_single_neg_mul_ofPS' (k : ℕ) (γ : PowerSeries T) :
    (∀ n : ℤ, n < -(k : ℤ) → (HahnSeries.single (-(k : ℤ)) (1 : T) * ofPS γ).coeff n = 0) ∧
      (HahnSeries.single (-(k : ℤ)) (1 : T) * ofPS γ).coeff (-(k : ℤ)) = PowerSeries.constantCoeff γ := by
  constructor
  · intro n hn
    rw [mul_comm, coeff_ofPS_mul_single', if_pos (by omega)]
  · rw [mul_comm, coeff_ofPS_mul_single', if_neg (by omega), ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    congr 1
    simp

theorem laurent_core (α a w u : PowerSeries T) (hα : α = PowerSeries.X * a) (ha : IsUnit (PowerSeries.constantCoeff a))
    (hwu : w * u = PowerSeries.X ^ 3) (hu : PowerSeries.constantCoeff u = 1) (hαs : PowerSeries.HasSubst α)
    (Lx Ly : LaurentSeries T)
    (hx : Lx * HahnSeries.ofPowerSeries ℤ T (-(PowerSeries.subst α w)) = HahnSeries.ofPowerSeries ℤ T (-α))
    (hy : Ly * HahnSeries.ofPowerSeries ℤ T (-(PowerSeries.subst α w)) = 1) :
    (∀ n : ℤ, n < -2 → Lx.coeff n = 0) ∧ IsUnit (Lx.coeff (-2)) ∧
      (∀ n : ℤ, n < -3 → Ly.coeff n = 0) ∧ IsUnit (Ly.coeff (-3)) := by

  have haU : IsUnit a := PowerSeries.isUnit_iff_constantCoeff.mpr ha
  have huU : IsUnit u := PowerSeries.isUnit_iff_constantCoeff.mpr (by rw [hu]; exact isUnit_one)
  obtain ⟨ai, hai⟩ : ∃ ai, a * ai = 1 := ⟨↑haU.unit⁻¹, haU.mul_val_inv⟩
  set su := PowerSeries.subst α u with hsu
  have hsuU : IsUnit su := by rw [hsu, ← PowerSeries.coe_substAlgHom hαs]; exact huU.map _

  have hsw : PowerSeries.subst α w * su = PowerSeries.X ^ 3 * a ^ 3 := by
    rw [hsu, ← PowerSeries.subst_mul hαs, hwu, ← PowerSeries.coe_substAlgHom hαs, map_pow,
      PowerSeries.coe_substAlgHom, PowerSeries.subst_X hαs, hα, mul_pow]

  set Z : LaurentSeries T := HahnSeries.single (1 : ℤ) (1 : T) with hZ
  set Zi : LaurentSeries T := HahnSeries.single (-1 : ℤ) (1 : T) with hZi
  have hZZi : Z * Zi = 1 := single_one_mul_single_neg_one'
  have hofX : ofPS PowerSeries.X = Z := HahnSeries.ofPowerSeries_X
  have haai : ofPS a * ofPS ai = 1 := by rw [← map_mul, hai, map_one]

  have ex : Lx * (Z ^ 3 * ofPS a ^ 3) = Z * ofPS a * ofPS su := by
    have := congrArg (fun v => - v * ofPS su) hx
    simp only [map_neg, mul_neg, neg_neg, neg_mul] at this
    rw [mul_assoc, ← map_mul, hsw, map_mul, map_pow, map_pow, hofX, hα, map_mul, hofX] at this
    rw [this]
  have ey : Ly * (Z ^ 3 * ofPS a ^ 3) = - ofPS su := by
    have := congrArg (fun v => - v * ofPS su) hy
    simp only [map_neg, mul_neg, neg_neg, neg_mul, one_mul] at this
    rw [mul_assoc, ← map_mul, hsw, map_mul, map_pow, map_pow, hofX] at this
    rw [this]
  have hU : IsUnit (Z ^ 3 * ofPS a ^ 3) :=
    ((IsUnit.of_mul_eq_one Zi hZZi).pow 3).mul ((haU.map (HahnSeries.ofPowerSeries ℤ T)).pow 3)

  have hLx : Lx = HahnSeries.single (-2 : ℤ) (1 : T) * ofPS (su * ai ^ 2) := by
    apply hU.mul_right_cancel
    rw [ex]
    have : (HahnSeries.single (-2 : ℤ) (1 : T) : LaurentSeries T) = Zi ^ 2 := by
      rw [hZi, HahnSeries.single_pow, one_pow]; norm_num
    rw [this, map_mul, map_pow]
    calc Z * ofPS a * ofPS su
        = Z * ofPS a * ofPS su * (Z * Zi) ^ 2 * (ofPS a * ofPS ai) ^ 2 := by rw [hZZi, haai]; ring
      _ = Zi ^ 2 * (ofPS su * ofPS ai ^ 2) * (Z ^ 3 * ofPS a ^ 3) := by ring
  have hLy : Ly = HahnSeries.single (-3 : ℤ) (1 : T) * ofPS (-(su * ai ^ 3)) := by
    apply hU.mul_right_cancel
    rw [ey]
    have : (HahnSeries.single (-3 : ℤ) (1 : T) : LaurentSeries T) = Zi ^ 3 := by
      rw [hZi, HahnSeries.single_pow, one_pow]; norm_num
    rw [this, map_neg, map_mul, map_pow]
    calc - ofPS su = - ofPS su * (Z * Zi) ^ 3 * (ofPS a * ofPS ai) ^ 3 := by rw [hZZi, haai]; ring
      _ = Zi ^ 3 * -(ofPS su * ofPS ai ^ 3) * (Z ^ 3 * ofPS a ^ 3) := by ring

  have haiU : IsUnit (PowerSeries.constantCoeff ai) :=
    IsUnit.of_mul_eq_one (PowerSeries.constantCoeff a) (by rw [mul_comm, ← map_mul, hai, map_one])
  have hsu0 : IsUnit (PowerSeries.constantCoeff su) := PowerSeries.isUnit_iff_constantCoeff.mp hsuU
  obtain ⟨h2a, h2b⟩ := coeff_single_neg_mul_ofPS' (T := T) 2 (su * ai ^ 2)
  obtain ⟨h3a, h3b⟩ := coeff_single_neg_mul_ofPS' (T := T) 3 (-(su * ai ^ 3))
  refine ⟨fun n hn => ?_, ?_, fun n hn => ?_, ?_⟩
  · rw [hLx]; exact h2a n (by exact_mod_cast hn)
  · rw [hLx, show (-2 : ℤ) = -((2 : ℕ) : ℤ) from rfl, h2b, map_mul, map_pow]
    exact hsu0.mul (haiU.pow 2)
  · rw [hLy]; exact h3a n (by exact_mod_cast hn)
  · rw [hLy, show (-3 : ℤ) = -((3 : ℕ) : ℤ) from rfl, h3b, map_neg, map_mul, map_pow]
    exact (hsu0.mul (haiU.pow 3)).neg

end LaurentCore

section Glue

open OverlapAux

theorem w3_main
    (T : Type) [CommRing T] [IsLocalRing T]
    (W W' : WeierstrassCurve T)
    (Ψ : projModelCR W.toProjective ≅ projModelCR W'.toProjective)
    (hΨ : Ψ.hom ≫ projModelStrCR W'.toProjective = projModelStrCR W.toProjective)
    (hΨO : (kwZeroSect T W).1 ≫ Ψ.hom = (kwZeroSect T W').1)
    (e : ZChartRing W'.toProjective →+* ZChartRing W.toProjective)
    (he : Spec.map (CommRingCat.ofHom e) ≫ zChartι W'.toProjective = zChartι W.toProjective ≫ Ψ.hom)
    (Φ : OriginChartRing W.toProjective →+* PowerSeries T)
    (hΦc : ∀ t : T, Φ (fromZeroRingHom (projModelGradingCR W.toProjective) _ (algebraMap T ((projModelGradingCR W.toProjective) 0) t)) =
      PowerSeries.C t)
    (hΦx : Φ (xOverY W.toProjective) = - PowerSeries.X) (hΦz : Φ (zOverY W.toProjective) = - W.formalW)
    (lam : ZChartRing W.toProjective →+* LaurentSeries T)
    (hlamc : ∀ t : T, lam (fromZeroRingHom (projModelGradingCR W.toProjective) _ (algebraMap T ((projModelGradingCR W.toProjective) 0) t)) =
      HahnSeries.C t)
    (hlamx : lam (xOverZ W.toProjective) * HahnSeries.ofPowerSeries ℤ T (Φ (zOverY W.toProjective)) =
      HahnSeries.ofPowerSeries ℤ T (Φ (xOverY W.toProjective)))
    (hlamy : lam (yOverZ W.toProjective) * HahnSeries.ofPowerSeries ℤ T (Φ (zOverY W.toProjective)) = 1) :
    (∀ n : ℤ, n < -2 → (lam (e (xOverZ W'.toProjective))).coeff n = 0) ∧
      IsUnit ((lam (e (xOverZ W'.toProjective))).coeff (-2)) ∧
      (∀ n : ℤ, n < -3 → (lam (e (yOverZ W'.toProjective))).coeff n = 0) ∧
      IsUnit ((lam (e (yOverZ W'.toProjective))).coeff (-3)) := by

  obtain ⟨Φ', hΦc', hΦx', hΦz'⟩ := WeierstrassCurve.DrinfeldGlobal.exists_ringHom_originChartRing_powerSeries W'
  obtain ⟨χ', hc', hx0, hz0, hχ'⟩ := exists_formalChart_of_iso W W' Ψ hΨ hΨO Φ hΦc hΦx hΦz

  have hwU : IsUnit (HahnSeries.ofPowerSeries ℤ T W.formalW) := by
    have h3 : IsUnit (HahnSeries.ofPowerSeries ℤ T (W.formalW * W.wUnitFactor)) := by
      rw [W.formalW_mul_wUnitFactor, map_pow, HahnSeries.ofPowerSeries_X]
      exact (IsUnit.of_mul_eq_one _ single_one_mul_single_neg_one').pow 3
    rw [map_mul] at h3
    exact isUnit_of_mul_isUnit_left h3
  have hunit : IsUnit (HahnSeries.ofPowerSeries ℤ T (Φ (zOverY W.toProjective))) := by
    rw [hΦz, map_neg]; exact hwU.neg
  have hO2 := OverlapAux.specMap_comp_zChartι_eq_of_laurent W.toProjective Φ hΦc lam hlamc hlamx hlamy hunit

  have hpt : Spec.map (CommRingCat.ofHom ((HahnSeries.ofPowerSeries ℤ T).comp χ')) ≫ originChartι W'.toProjective =
      Spec.map (CommRingCat.ofHom (lam.comp e)) ≫ zChartι W'.toProjective := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hχ', CommRingCat.ofHom_comp, Spec.map_comp,
      Category.assoc, he, ← Category.assoc (Spec.map (CommRingCat.ofHom lam)), hO2, CommRingCat.ofHom_comp,
      Spec.map_comp]
    simp only [Category.assoc]
  obtain ⟨h1, h2⟩ := OverlapAux.zChart_mul_originChart_of_specMap_comp_eq W'.toProjective
    ((HahnSeries.ofPowerSeries ℤ T).comp χ') (lam.comp e) hpt
  simp only [RingHom.comp_apply] at h1 h2

  set α : PowerSeries T := - χ' (xOverY W'.toProjective) with hα
  have hξ : χ' (xOverY W'.toProjective) = - α := by rw [hα, neg_neg]
  have hζ : χ' (zOverY W'.toProjective) = - PowerSeries.subst α W'.formalW :=
    formalChart_zOverY_eq W' χ' hc' hx0 hz0 Φ' hΦc' hΦx' hΦz'
  rw [hξ, hζ] at h1
  rw [hζ] at h2
  have hα0 : PowerSeries.constantCoeff α = 0 := by rw [hα, map_neg, hx0, neg_zero]
  have hαs : PowerSeries.HasSubst α := PowerSeries.HasSubst.of_constantCoeff_zero' hα0
  obtain ⟨a, ha⟩ := PowerSeries.X_dvd_iff.mpr hα0
  have haU : IsUnit (PowerSeries.constantCoeff a) := by
    have h := isUnit_coeff_one_formalChart W W' Ψ hΨ hΨO Φ hΦc hΦx hΦz Φ' hΦc' hΦx' hΦz' χ' hc' hx0 hz0 hχ'
    rw [hξ, ha, map_neg, show (1 : ℕ) = 0 + 1 from rfl, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_zero_eq_constantCoeff_apply] at h
    simpa using h
  exact laurent_core α a W'.formalW W'.wUnitFactor ha haU W'.formalW_mul_wUnitFactor W'.constantCoeff_wUnitFactor hαs
    _ _ h1 h2

end Glue

end WMLocal

theorem solution
    (T : Type) [CommRing T] [IsLocalRing T]
    (W W' : WeierstrassCurve T)
    (Ψ : projModelCR W.toProjective ≅ projModelCR W'.toProjective)
    (hΨ : Ψ.hom ≫ projModelStrCR W'.toProjective = projModelStrCR W.toProjective)
    (hΨO : (kwZeroSect T W).1 ≫ Ψ.hom = (kwZeroSect T W').1)
    (e : ZChartRing W'.toProjective →+* ZChartRing W.toProjective)
    (he : Spec.map (CommRingCat.ofHom e) ≫ zChartι W'.toProjective = zChartι W.toProjective ≫ Ψ.hom)
    (Φ : OriginChartRing W.toProjective →+* PowerSeries T)
    (hΦc : ∀ t : T, Φ (fromZeroRingHom (projModelGradingCR W.toProjective) _ (algebraMap T ((projModelGradingCR W.toProjective) 0) t)) =
      PowerSeries.C t)
    (hΦx : Φ (xOverY W.toProjective) = - PowerSeries.X) (hΦz : Φ (zOverY W.toProjective) = - W.formalW)
    (lam : ZChartRing W.toProjective →+* LaurentSeries T)
    (hlamc : ∀ t : T, lam (fromZeroRingHom (projModelGradingCR W.toProjective) _ (algebraMap T ((projModelGradingCR W.toProjective) 0) t)) =
      HahnSeries.C t)
    (hlamx : lam (xOverZ W.toProjective) * HahnSeries.ofPowerSeries ℤ T (Φ (zOverY W.toProjective)) =
      HahnSeries.ofPowerSeries ℤ T (Φ (xOverY W.toProjective)))
    (hlamy : lam (yOverZ W.toProjective) * HahnSeries.ofPowerSeries ℤ T (Φ (zOverY W.toProjective)) = 1) :
    (∀ n : ℤ, n < -2 → (lam (e (xOverZ W'.toProjective))).coeff n = 0) ∧
      IsUnit ((lam (e (xOverZ W'.toProjective))).coeff (-2)) ∧
      (∀ n : ℤ, n < -3 → (lam (e (yOverZ W'.toProjective))).coeff n = 0) ∧
      IsUnit ((lam (e (yOverZ W'.toProjective))).coeff (-3)) :=
  WMLocal.w3_main T W W' Ψ hΨ hΨO e he Φ hΦc hΦx hΦz lam hlamc hlamx hlamy

end S_WeierstrassProjModel_coeff_laurent_zChart_of_iso_of_kwZeroSect_comp_eq
end P2MW
export P2MW.S_WeierstrassProjModel_coeff_laurent_zChart_of_iso_of_kwZeroSect_comp_eq (solution)
