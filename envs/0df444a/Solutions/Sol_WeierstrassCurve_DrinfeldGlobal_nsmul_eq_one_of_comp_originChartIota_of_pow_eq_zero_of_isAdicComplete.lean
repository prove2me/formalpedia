-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.nsmul_eq_one_of_comp_originChartIota_of_pow_eq_zero_of_isAdicComplete
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/2717ab8d-03ce-54bd-b1df-9f7165568994

import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor

import Theorems.Thm_WeierstrassProjModel_exists_isCoefficientHom
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isPullback_projMap_of_isCoefficientHom
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_comp_projMap_eq_of_isOriginChartSection
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_comp_projMap_mul_eq_mul_comp_projMap_of_one_comp_eq
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_nsmul_eq_one_iff_X_sub_C_originParam_dvd_nthSeries
import Theorems.Thm_WeierstrassCurve_exists_formalGroup_isComm_toPowerSeries_eq
import Theorems.Thm_FormalGroup_exists_nthSeries_eq_qfold_of_isUnit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_nsmul_eq_one_of_comp_originChartIota_of_pow_eq_zero_of_isAdicComplete
p2m_attr_erase "simp" "FormalGroup.LawIso.mk.sizeOf_spec FormalGroup.LawHom.mk.sizeOf_spec FormalGroup.LawHom.mk.injEq FormalGroup.LawIso.mk.injEq WeierstrassProjModel.kw_lrThird_substHom_X"

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal
attribute [local instance] MvPolynomial.gradedAlgebra

open IsLocalRing HomogeneousLocalization

namespace FrobKerAux

theorem exists_originChart_comp_projMap
    {T T' : Type} [CommRing T] [CommRing T'] (W : WeierstrassCurve.Projective T) (f : T →+* T')
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

theorem exists_isOriginChartSection_comp_eq
    {T T' : Type} [CommRing T] [CommRing T'] (W : WeierstrassCurve.Projective T) (f : T →+* T')
    (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f))
    (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f)) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ)
    (hcoef : IsCoefficientHom W f φ)
    (a : OriginChartRing W →+* OriginChartRing (W.map f))
    (ha : originChartι (W.map f) ≫ Proj.map φ hφ = Spec.map (CommRingCat.ofHom a) ≫ originChartι W)
    (S : Section (W.map f)) (χ : OriginChartRing W →+* T')
    (hS : S.1 ≫ Proj.map φ hφ = Spec.map (CommRingCat.ofHom χ) ≫ originChartι W) :
    ∃ χ' : OriginChartRing (W.map f) →+* T', IsOriginChartSection S χ' ∧ χ'.comp a = χ := by
  classical
  obtain ⟨-, hX⟩ := hcoef
  have hrange : Set.range S.1 ⊆ Set.range (originChartι (W.map f)) := by
    rintro _ ⟨p, rfl⟩
    have hp : (Proj.map φ hφ) (S.1 p) ∈ (originChartι W).opensRange := by
      rw [Scheme.Hom.mem_opensRange]
      refine ⟨Spec.map (CommRingCat.ofHom χ) p, ?_⟩
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hS]
    have hp' : S.1 p ∈ (originChartι (W.map f)).opensRange := by
      have e1 : (originChartι W).opensRange = Proj.basicOpen (projModelGradingCR W) (coord W 1) :=
        Proj.opensRange_awayι _ _ _ _
      have e2 : (originChartι (W.map f)).opensRange =
          Proj.basicOpen (projModelGradingCR (W.map f)) (coord (W.map f) 1) :=
        Proj.opensRange_awayι _ _ _ _
      rw [e1] at hp
      have hc : φ (coord W 1) = coord (W.map f) 1 := hX 1
      rw [e2, ← hc, ← Proj.map_preimage_basicOpen φ hφ]
      exact hp
    rw [Scheme.Hom.mem_opensRange] at hp'
    exact hp'
  set l := IsOpenImmersion.lift (originChartι (W.map f)) S.1 hrange with hl_def
  have hl : l ≫ originChartι (W.map f) = S.1 := IsOpenImmersion.lift_fac _ _ _
  set χ' : OriginChartRing (W.map f) →+* T' := (Spec.preimage l).hom with hχ'
  have hSpecχ' : Spec.map (CommRingCat.ofHom χ') = l := by
    rw [hχ', CommRingCat.ofHom_hom, Spec.map_preimage]
  refine ⟨χ', ?_, ?_⟩
  · show S.1 = Spec.map (CommRingCat.ofHom χ') ≫ originChartι (W.map f)
    rw [hSpecχ', hl]
  · have e1 : Spec.map (CommRingCat.ofHom (χ'.comp a)) ≫ originChartι W =
        Spec.map (CommRingCat.ofHom χ) ≫ originChartι W := by
      rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, ← ha, ← Category.assoc, hSpecχ', hl, hS]
    have e2 := Spec.map_injective ((cancel_mono (originChartι W)).mp e1)
    have e3 := congrArg CommRingCat.Hom.hom e2
    simpa only [CommRingCat.hom_ofHom] using e3

theorem nsmul_comp_projMap
    {T T' : Type} [CommRing T] [CommRing T'] (V : WeierstrassCurve.Projective T) [V.toAffine.IsElliptic]
    (f : T →+* T')
    (φ : projModelGradingCR V →+*ᵍ projModelGradingCR (V.map f))
    (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (V.map f)) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR V)).map φ)
    (hcoef : IsCoefficientHom V f φ)
    (G : RelativeGroupLaw T (projModelStrCR V)) (L : RelativeGroupLaw T' (projModelStrCR (V.map f)))
    (h1 : (L.one (𝟙 (Spec (CommRingCat.of T')))).1 ≫ Proj.map φ hφ =
      Spec.map (CommRingCat.ofHom f) ≫ (G.one (𝟙 (Spec (CommRingCat.of T)))).1)
    (hsq : Proj.map φ hφ ≫ projModelStrCR V = projModelStrCR (V.map f) ≫ Spec.map (CommRingCat.ofHom f))
    (n : ℕ) (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of T'))) (projModelStrCR (V.map f))) :
    (L.nsmul (𝟙 _) n a).1 ≫ Proj.map φ hφ =
      (G.nsmul (𝟙 _ ≫ Spec.map (CommRingCat.ofHom f)) n
        ⟨a.1 ≫ Proj.map φ hφ, by rw [Category.assoc, hsq, ← Category.assoc, a.2]⟩).1 := by
  induction n with
  | zero =>
    show (L.one _).1 ≫ Proj.map φ hφ = (G.one _).1
    rw [h1]
    have := G.one_natural (𝟙 _) (𝟙 _ ≫ Spec.map (CommRingCat.ofHom f)) (𝟙 _ ≫ Spec.map (CommRingCat.ofHom f))
      (Category.comp_id _)
    rw [← this, schemeHomOverComp_coe, Category.id_comp]
  | succ n ih =>
    show (L.mul _ (L.nsmul _ n a) a).1 ≫ Proj.map φ hφ = (G.mul _ (G.nsmul _ n _) _).1
    rw [WeierstrassCurve.DrinfeldGlobal.comp_projMap_mul_eq_mul_comp_projMap_of_one_comp_eq V f φ hφ hcoef G L h1 hsq
      (𝟙 _) (L.nsmul _ n a) a]
    congr 2
    exact Subtype.ext ih

end FrobKerAux

open FrobKerAux

theorem solution
    (A : Type) [CommRing A] (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (q : ℕ) [Fact q.Prime]
    (T : Type) [CommRing T] [Algebra A T] [CharP T q]
    (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ)
    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (ρ : T →+* R)
    (x : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (projModelStrCR W.toProjective))
    (χ : OriginChartRing W.toProjective →+* R)
    (hx : x.1 = Spec.map (CommRingCat.ofHom χ) ≫ originChartι W.toProjective)
    (hX : (χ (xOverY W.toProjective)) ^ q = 0) (hZ : (χ (zOverY W.toProjective)) ^ q = 0) :
    (𝒢 T W hΔ).nsmul _ q x = (𝒢 T W hΔ).one _ := by
  classical
  have hΔ' : IsUnit (W.map ρ).Δ := by rw [WeierstrassCurve.map_Δ]; exact hΔ.map ρ
  letI algAR : Algebra A R := (ρ.comp (algebraMap A T)).toAlgebra
  haveI hE : (W.map ρ).IsElliptic := ⟨hΔ'⟩
  haveI hE0 : W.toProjective.toAffine.IsElliptic := ⟨hΔ⟩
  obtain ⟨φ, hφ, hcoef⟩ := WeierstrassProjModel.exists_isCoefficientHom W.toProjective ρ
  have hpb := WeierstrassCurve.DrinfeldGlobal.isPullback_projMap_of_isCoefficientHom W.toProjective ρ φ hφ hcoef
  have hsq : Proj.map φ hφ ≫ projModelStrCR W.toProjective =
      projModelStrCR (W.toProjective.map ρ) ≫ Spec.map (CommRingCat.ofHom ρ) := hpb.w

  obtain ⟨x', hx'⟩ : ∃ x' : Section (W.toProjective.map ρ), x'.1 ≫ Proj.map φ hφ = x.1 := by
    have wx : x.1 ≫ projModelStrCR W.toProjective = 𝟙 _ ≫ Spec.map (CommRingCat.ofHom ρ) := by
      rw [Category.id_comp]; exact x.2
    exact ⟨⟨hpb.lift x.1 (𝟙 _) wx, hpb.lift_snd _ _ _⟩, hpb.lift_fst _ _ _⟩

  obtain ⟨a, ha, hax, haz⟩ := exists_originChart_comp_projMap W.toProjective ρ φ hφ hcoef
  obtain ⟨χ', hχ'sec, hχ'a⟩ := exists_isOriginChartSection_comp_eq W.toProjective ρ φ hφ hcoef a ha x' χ
    (by rw [hx', hx])
  have hχ'x : χ' (xOverY (W.toProjective.map ρ)) = χ (xOverY W.toProjective) := by
    rw [← hax, ← RingHom.comp_apply, hχ'a]
  have hχ'z : χ' (zOverY (W.toProjective.map ρ)) = χ (zOverY W.toProjective) := by
    rw [← haz, ← RingHom.comp_apply, hχ'a]
  have hnil : ∀ r : R, r ^ q = 0 → r ∈ maximalIdeal R := by
    intro r hr
    rw [IsLocalRing.mem_maximalIdeal]
    intro hu
    have : IsUnit ((0 : R)) := hr ▸ hu.pow q
    exact not_isUnit_zero this
  have hred : ReducesToOrigin x' χ' (maximalIdeal R) := by
    unfold ReducesToOrigin originParam originW
    refine ⟨hχ'sec, (maximalIdeal R).neg_mem ?_, (maximalIdeal R).neg_mem ?_⟩
    · rw [hχ'x]; exact hnil _ hX
    · rw [hχ'z]; exact hnil _ hZ

  obtain ⟨F, hFc, hFW⟩ := WeierstrassCurve.exists_formalGroup_isComm_toPowerSeries_eq (W.map ρ)
  haveI := hFc
  have hGpts := h𝒢 R (W.map ρ) hΔ'
  have hGone := h𝒢O R (W.map ρ) hΔ'
  have htor := WeierstrassCurve.DrinfeldGlobal.nsmul_eq_one_iff_X_sub_C_originParam_dvd_nthSeries
    (W.map ρ) F hFW (𝒢 R (W.map ρ) hΔ') hGpts hGone q x' χ' hred

  have hq0 : ((q : ℕ) : R) = 0 := by
    rw [← map_natCast ρ, CharP.cast_eq_zero, map_zero]
  have hunit : ∀ k : ℕ, 1 ≤ k → ¬ q ∣ k → IsUnit (k : R) := by
    intro k _ hqk
    have hcop : Nat.Coprime k q := ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hqk).symm
    obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hcop
    have h' : ((u : ℤ) : R) * (k : R) = 1 := by
      have := congrArg (Int.cast : ℤ → R) huv
      push_cast at this
      rw [hq0, mul_zero, add_zero] at this
      exact this
    rw [mul_comm] at h'
    exact isUnit_iff_exists_inv.mpr ⟨_, h'⟩
  obtain ⟨h, g, hqf⟩ := FormalGroup.exists_nthSeries_eq_qfold_of_isUnit F (Nat.Prime.two_le Fact.out) hunit
  have hnth : F.nthSeries q = PowerSeries.X ^ q * g := by
    rw [hqf, nsmul_eq_mul, hq0, zero_smul, add_zero]
    have : ((q : ℕ) : PowerSeries R) = 0 := by
      rw [← map_natCast (PowerSeries.C (R := R)), hq0, map_zero]
    rw [this, zero_mul, zero_add]
  have hzq : (originParam χ') ^ q = 0 := by
    unfold originParam
    rw [neg_pow, hχ'x, hX, mul_zero]
  have hdvd : (PowerSeries.X - PowerSeries.C (originParam χ')) ∣ F.nthSeries q := by
    rw [hnth]
    refine Dvd.dvd.mul_right ?_ g
    have := sub_dvd_pow_sub_pow (PowerSeries.X : PowerSeries R) (PowerSeries.C (originParam χ')) q
    rwa [← map_pow, hzq, map_zero, sub_zero] at this
  have hx'q : (𝒢 R (W.map ρ) hΔ').nsmul (𝟙 _) q x' = (𝒢 R (W.map ρ) hΔ').one (𝟙 _) := htor.2 hdvd

  obtain ⟨χ0, hχ0, hχ0x, hχ0z⟩ := h𝒢O T W hΔ
  obtain ⟨χ1, hχ1, hχ1x, hχ1z⟩ := h𝒢O R (W.map ρ) hΔ'
  have h1 := WeierstrassCurve.DrinfeldGlobal.comp_projMap_eq_of_isOriginChartSection W.toProjective ρ φ hφ hcoef
    ((𝒢 T W hΔ).one (𝟙 _)) ((𝒢 R (W.map ρ) hΔ').one (𝟙 _)) χ0 hχ0 hχ0x hχ0z χ1 hχ1 hχ1x hχ1z
  have htr := nsmul_comp_projMap W.toProjective ρ φ hφ hcoef (𝒢 T W hΔ) (𝒢 R (W.map ρ) hΔ') h1 hsq q x'
  rw [hx'q, h1] at htr

  apply Subtype.ext
  have e1 : ((𝒢 T W hΔ).nsmul (Spec.map (CommRingCat.ofHom ρ)) q x).1 =
      ((𝒢 T W hΔ).nsmul (𝟙 _ ≫ Spec.map (CommRingCat.ofHom ρ)) q (schemeHomOverComp (𝟙 _) rfl x)).1 := by
    rw [← (𝒢 T W hΔ).nsmul_natural _ (𝟙 _ ≫ Spec.map (CommRingCat.ofHom ρ)) (𝟙 _) rfl q x,
      schemeHomOverComp_coe, Category.id_comp]
  have e2 : ((𝒢 T W hΔ).one (Spec.map (CommRingCat.ofHom ρ))).1 =
      ((𝒢 T W hΔ).one (𝟙 _ ≫ Spec.map (CommRingCat.ofHom ρ))).1 := by
    rw [← (𝒢 T W hΔ).one_natural _ (𝟙 _ ≫ Spec.map (CommRingCat.ofHom ρ)) (𝟙 _) rfl,
      schemeHomOverComp_coe, Category.id_comp]
  have e3 : schemeHomOverComp (𝟙 _) (rfl : 𝟙 _ ≫ Spec.map (CommRingCat.ofHom ρ) = _) x =
      (⟨x'.1 ≫ Proj.map φ hφ, by rw [Category.assoc, hsq, ← Category.assoc, x'.2]⟩ :
        SchemeHomOver (𝟙 _ ≫ Spec.map (CommRingCat.ofHom ρ)) (projModelStrCR W.toProjective)) := by
    apply Subtype.ext
    show 𝟙 _ ≫ x.1 = x'.1 ≫ Proj.map φ hφ
    rw [Category.id_comp, hx']
  have e4 : ((𝒢 T W hΔ).one (𝟙 _ ≫ Spec.map (CommRingCat.ofHom ρ))).1 =
      (𝟙 _ ≫ Spec.map (CommRingCat.ofHom ρ)) ≫ ((𝒢 T W hΔ).one (𝟙 _)).1 := by
    rw [← (𝒢 T W hΔ).one_natural (𝟙 _) (𝟙 _ ≫ Spec.map (CommRingCat.ofHom ρ))
      (𝟙 _ ≫ Spec.map (CommRingCat.ofHom ρ)) (Category.comp_id _), schemeHomOverComp_coe]
  rw [e1, e2, e3, ← htr, e4, Category.id_comp]

end S_WeierstrassCurve_DrinfeldGlobal_nsmul_eq_one_of_comp_originChartIota_of_pow_eq_zero_of_isAdicComplete
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_nsmul_eq_one_of_comp_originChartIota_of_pow_eq_zero_of_isAdicComplete (solution)
