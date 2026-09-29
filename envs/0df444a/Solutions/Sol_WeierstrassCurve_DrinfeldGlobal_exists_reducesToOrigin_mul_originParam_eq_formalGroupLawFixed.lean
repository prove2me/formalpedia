-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.exists_reducesToOrigin_mul_originParam_eq_formalGroupLawFixed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/93666ea1-af96-5515-bc30-e5c8593dda57

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_FormalGroup
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Theorems.Thm_WeierstrassProjModel_exists_isPointsEval_apply_eq_some_of_eq_comp_zChartInclusion_of_isDomain
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_section_eq_of_specMap_comp_eq_of_injective
import Theorems.Thm_WeierstrassCurve_exists_genericPoint_formalGroupLawFixed_eq_add
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_ringHom_originChartRing_eq
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_originChart_rel
import Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_exists_isOriginChartSection_iff_one_eq_kwZeroSect
import Theorems.Thm_MvPowerSeries_isNoetherianRing_of_finite
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_originChart_rel_unique_of_constantCoeff_eq_zero
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_eq_comp_zChartInclusion_of_eq_comp_originChartInclusion
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_reducesToOrigin_mul_originParam_eq_formalGroupLawFixed
p2m_attr_erase "simp" "WeierstrassProjModel.kw_lrThird_substHom_X WeierstrassCurve.DrinfeldGlobal.LevelTransport.mk.injEq WeierstrassCurve.DrinfeldGlobal.LevelTransport.mk.sizeOf_spec"

set_option autoImplicit false

p2m_open "AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_reducesToOrigin_mul_originParam_eq_formalGroupLawFixed.WeierstrassCurve.DrinfeldGlobal IsLocalRing"

attribute [local instance] MvPolynomial.gradedAlgebra

attribute [local instance] WeierstrassProjModel.kw_pbac_awayAlgebra

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine toProjective a₃ map_map a₁ map a₄ a₂ a₆ Affine.Point.some map_id toAffine Affine.Point map_injective map_a₆ map_a₁ map_a₄ map_a₂ baseChange map_a₃ formalW constantCoeff_formalW formalW_eq formalGroupLawFixed constantCoeff_formalGroupLawFixed fgGenW GenK genι genW genericPoint DrinfeldGlobal.section_eq_of_specMap_comp_eq_of_injective exists_genericPoint_formalGroupLawFixed_eq_add DrinfeldGlobal.exists_ringHom_originChartRing_eq DrinfeldGlobal.originChart_rel DrinfeldGlobal.originChart_rel_unique_of_constantCoeff_eq_zero DrinfeldGlobal.exists_eq_comp_zChartInclusion_of_eq_comp_originChartInclusion"
namespace DrinfeldGlobal
p2m_export "WeierstrassCurve.DrinfeldGlobal" "base Section OriginChartRing originChartι xOverY zOverY IsOriginChartSection originParam originW ReducesToOrigin xOverZ yOverZ section_eq_of_specMap_comp_eq_of_injective exists_ringHom_originChartRing_eq originChart_rel originChart_rel_unique_of_constantCoeff_eq_zero exists_eq_comp_zChartInclusion_of_eq_comp_originChartInclusion"
namespace UnivFormalAdd
p2m_open "WeierstrassCurve.DrinfeldGlobal WeierstrassCurve"

open MvPolynomial HomogeneousLocalization NeronModelInfra

section SpanX

variable {A : Type} [CommRing A]

theorem constantCoeff_eq_zero_of_mem_span_X {f : MvPowerSeries (Fin 2) A}
    (hf : f ∈ Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) A), MvPowerSeries.X 1}) :
    MvPowerSeries.constantCoeff f = 0 := by
  have hle : Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) A), MvPowerSeries.X 1} ≤
      RingHom.ker (MvPowerSeries.constantCoeff (σ := Fin 2) (R := A)) := by
    rw [Ideal.span_le]
    rintro g hg
    rcases hg with rfl | rfl
    · simp [RingHom.mem_ker, MvPowerSeries.constantCoeff_X]
    · simp [RingHom.mem_ker, MvPowerSeries.constantCoeff_X]
  exact hle hf

theorem mem_span_X_of_constantCoeff_eq_zero (f : MvPowerSeries (Fin 2) A)
    (hf : MvPowerSeries.constantCoeff f = 0) :
    f ∈ Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) A), MvPowerSeries.X 1} := by
  classical

  let r : MvPowerSeries (Fin 2) A := fun m ↦ if m 0 = 0 then MvPowerSeries.coeff m f else 0
  have hr : ∀ m : Fin 2 →₀ ℕ, MvPowerSeries.coeff m r = if m 0 = 0 then MvPowerSeries.coeff m f else 0 := fun m ↦ rfl
  have h0 : (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) A) ∣ f - r := by
    rw [MvPowerSeries.X_dvd_iff]
    intro m hm
    rw [map_sub, hr m, if_pos hm, sub_self]
  have h1 : (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) A) ∣ r := by
    rw [MvPowerSeries.X_dvd_iff]
    intro m hm
    rw [hr m]
    split_ifs with hm0
    · have : m = 0 := by
        ext i; fin_cases i <;> simp [hm0, hm]
      rw [this]; exact hf
    · rfl
  have : f = (f - r) + r := by ring
  rw [this]
  refine Ideal.add_mem _ ?_ ?_
  · obtain ⟨g, hg⟩ := h0
    rw [hg]; exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert _ _))
  · obtain ⟨g, hg⟩ := h1
    rw [hg]; exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))

end SpanX

section Chart

variable {T : Type} [CommRing T]

theorem apply_sc_eq (W : WeierstrassCurve T) (P : Section W) (χ : OriginChartRing W →+* T)
    (hχ : IsOriginChartSection P χ) (t : T) :
    χ (fromZeroRingHom (projModelGradingCR W) _ (algebraMap T ((projModelGradingCR W) 0) t)) = t := by
  have h := P.2
  rw [hχ] at h
  simp only [projModelStrCR, Category.assoc, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp] at h
  have h2 : Spec.map (CommRingCat.ofHom (algebraMap T ((projModelGradingCR W) 0)) ≫
      CommRingCat.ofHom (fromZeroRingHom (projModelGradingCR W) _) ≫ CommRingCat.ofHom χ) =
      Spec.map (𝟙 _) := by rw [Spec.map_id]; exact h
  have h3 := Spec.map_injective h2
  have h4 := congrArg (fun g : CommRingCat.of T ⟶ CommRingCat.of T ↦ g.hom t) h3
  simpa using h4

noncomputable def sectionOfChart (W : WeierstrassCurve T) (χ : OriginChartRing W →+* T)
    (hsc : ∀ t : T, χ (fromZeroRingHom (projModelGradingCR W) _ (algebraMap T ((projModelGradingCR W) 0) t)) = t) :
    Section W :=
  ⟨Spec.map (CommRingCat.ofHom χ) ≫ originChartι W, by
    have hid : χ.comp ((fromZeroRingHom (projModelGradingCR W.toProjective) _).comp
        (algebraMap T (projModelGradingCR W.toProjective 0))) = RingHom.id T := RingHom.ext hsc
    simp only [projModelStrCR, Category.assoc]
    rw [← Category.assoc (Proj.awayι ..), Proj.awayι_toSpecZero, ← Spec.map_comp,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      hid, CommRingCat.ofHom_id, Spec.map_id]⟩

theorem isOriginChartSection_sectionOfChart (W : WeierstrassCurve T) (χ : OriginChartRing W →+* T)
    (hsc : ∀ t : T, χ (fromZeroRingHom (projModelGradingCR W) _ (algebraMap T ((projModelGradingCR W) 0) t)) = t) :
    IsOriginChartSection (sectionOfChart W χ hsc) χ := rfl

end Chart

section Points

variable {K : Type} [Field K] [DecidableEq K]

theorem some_eq_some {V : WeierstrassCurve K} {x y x' y' : K} (hx : x = x') (hy : y = y')
    (h : V.toAffine.Nonsingular x y) (h' : V.toAffine.Nonsingular x' y') :
    WeierstrassCurve.Affine.Point.some x y h = WeierstrassCurve.Affine.Point.some x' y' h' := by
  subst hx hy; rfl

theorem some_add_some_transfer :
    ∀ {V V' : WeierstrassCurve K} (_ : V = V') {x₁ y₁ x₂ y₂ x₃ y₃ : K}
      (h₁ : V.toAffine.Nonsingular x₁ y₁) (h₂ : V.toAffine.Nonsingular x₂ y₂) (h₃ : V.toAffine.Nonsingular x₃ y₃)
      (h₁' : V'.toAffine.Nonsingular x₁ y₁) (h₂' : V'.toAffine.Nonsingular x₂ y₂)
      (h₃' : V'.toAffine.Nonsingular x₃ y₃),
      WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ + WeierstrassCurve.Affine.Point.some x₂ y₂ h₂ =
        WeierstrassCurve.Affine.Point.some x₃ y₃ h₃ →
      WeierstrassCurve.Affine.Point.some x₁ y₁ h₁' + WeierstrassCurve.Affine.Point.some x₂ y₂ h₂' =
        WeierstrassCurve.Affine.Point.some x₃ y₃ h₃' := by
  rintro V _ rfl _ _ _ _ _ _ h₁ h₂ h₃ h₁' h₂' h₃' h
  exact h

end Points

section Formal

variable {A : Type} [CommRing A] (W : WeierstrassCurve A)

theorem neg_fgGenW_rel {σ : Type} (z : MvPowerSeries σ A) (hz : MvPowerSeries.constantCoeff z = 0) :
    (-(W.fgGenW z)) + algebraMap A _ W.a₁ * (-z) * (-(W.fgGenW z)) + algebraMap A _ W.a₃ * (-(W.fgGenW z)) ^ 2 =
      (-z) ^ 3 + algebraMap A _ W.a₂ * (-z) ^ 2 * (-(W.fgGenW z)) +
        algebraMap A _ W.a₄ * (-z) * (-(W.fgGenW z)) ^ 2 + algebraMap A _ W.a₆ * (-(W.fgGenW z)) ^ 3 := by
  have ht : PowerSeries.HasSubst z := PowerSeries.HasSubst.of_constantCoeff_zero hz
  have h := congrArg (PowerSeries.substAlgHom ht) W.formalW_eq
  simp only [map_add, map_mul, map_pow, PowerSeries.substAlgHom_X, PowerSeries.coe_substAlgHom,
    PowerSeries.subst_C] at h
  have hC : ∀ a : A, (MvPowerSeries.C a : MvPowerSeries σ A) = algebraMap A _ a := fun a ↦ rfl
  simp only [hC] at h
  rw [show PowerSeries.subst z W.formalW = W.fgGenW z from rfl] at h
  linear_combination (-1 : MvPowerSeries σ A) * h

theorem constantCoeff_fgGenW {σ : Type} (z : MvPowerSeries σ A) (hz : MvPowerSeries.constantCoeff z = 0) :
    MvPowerSeries.constantCoeff (W.fgGenW z) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero hz _ W.constantCoeff_formalW

end Formal

end WeierstrassCurve.DrinfeldGlobal.UnivFormalAdd

open WeierstrassCurve.DrinfeldGlobal.UnivFormalAdd HomogeneousLocalization NeronModelInfra in
set_option maxHeartbeats 6400000 in
theorem solution
    {A : Type} [CommRing A] [IsDomain A] [IsNoetherianRing A] (W : WeierstrassCurve A) [W.IsElliptic]
    (G₀ : RelativeGroupLaw (MvPowerSeries (Fin 2) A)
      (projModelStrCR (W.map (algebraMap A (MvPowerSeries (Fin 2) A)))))
    (hGpts : ∃ ev, IsPointsEval (W.map (algebraMap A (MvPowerSeries (Fin 2) A))) G₀ ev)
    (hGone : ∃ χ : OriginChartRing (W.map (algebraMap A (MvPowerSeries (Fin 2) A))) →+* MvPowerSeries (Fin 2) A,
      IsOriginChartSection (G₀.one (𝟙 _)) χ ∧
        χ (xOverY (W.map (algebraMap A (MvPowerSeries (Fin 2) A)))) = 0 ∧
        χ (zOverY (W.map (algebraMap A (MvPowerSeries (Fin 2) A)))) = 0)
    (P₁ P₂ : Section (W.map (algebraMap A (MvPowerSeries (Fin 2) A))))
    (χ₁ χ₂ : OriginChartRing (W.map (algebraMap A (MvPowerSeries (Fin 2) A))) →+* MvPowerSeries (Fin 2) A)
    (h₁ : ReducesToOrigin P₁ χ₁ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) A), MvPowerSeries.X 1}))
    (h₂ : ReducesToOrigin P₂ χ₂ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) A), MvPowerSeries.X 1}))
    (hz₁ : originParam χ₁ = MvPowerSeries.X 0) (hz₂ : originParam χ₂ = MvPowerSeries.X 1) :
    ∃ χ : OriginChartRing (W.map (algebraMap A (MvPowerSeries (Fin 2) A))) →+* MvPowerSeries (Fin 2) A,
      ReducesToOrigin (G₀.mul (𝟙 _) P₁ P₂) χ
        (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) A), MvPowerSeries.X 1}) ∧
      originParam χ = W.formalGroupLawFixed := by
  classical

  haveI : IsNoetherianRing (MvPowerSeries (Fin 2) A) := MvPowerSeries.isNoetherianRing_of_finite
  haveI : IsDomain (MvPowerSeries (Fin 2) A) := NoZeroDivisors.to_isDomain _
  have hone : (G₀.one (𝟙 _)).1 = (kwZeroSect (MvPowerSeries (Fin 2) A) (W.map (algebraMap A (MvPowerSeries (Fin 2) A)))).1 :=
    (WeierstrassProjModel.RelativeGroupLaw.exists_isOriginChartSection_iff_one_eq_kwZeroSect (W.map (algebraMap A (MvPowerSeries (Fin 2) A))) G₀).mp hGone
  obtain ⟨ev, hev, hev0, hevc⟩ :=
    WeierstrassProjModel.exists_isPointsEval_apply_eq_some_of_eq_comp_zChartInclusion_of_isDomain (W.map (algebraMap A (MvPowerSeries (Fin 2) A))) G₀ hone

  have htK : Spec.map (CommRingCat.ofHom (algebraMap (MvPowerSeries (Fin 2) A) (WeierstrassCurve.GenK (Fin 2) A))) ≫ 𝟙 _ =
      Spec.map (CommRingCat.ofHom (algebraMap (MvPowerSeries (Fin 2) A) (WeierstrassCurve.GenK (Fin 2) A))) := Category.comp_id _
  have hF0 : MvPowerSeries.constantCoeff W.formalGroupLawFixed = 0 := W.constantCoeff_formalGroupLawFixed
  obtain ⟨hwF, hw0, hw1, hsum⟩ := WeierstrassCurve.exists_genericPoint_formalGroupLawFixed_eq_add W
  have ecurve : W.genW (Fin 2) = ((W.map (algebraMap A (MvPowerSeries (Fin 2) A)))).toProjective.baseChange (WeierstrassCurve.GenK (Fin 2) A) := by
    show W.map _ = (W.map _).map _
    rw [WeierstrassCurve.map_map, ← IsScalarTower.algebraMap_eq]

  have read : ∀ (P : Section (W.map (algebraMap A (MvPowerSeries (Fin 2) A)))) (χ : OriginChartRing (W.map (algebraMap A (MvPowerSeries (Fin 2) A))) →+* (MvPowerSeries (Fin 2) A)) (z w : (MvPowerSeries (Fin 2) A)),
      IsOriginChartSection P χ → χ (xOverY (W.map (algebraMap A (MvPowerSeries (Fin 2) A)))) = -z → χ (zOverY (W.map (algebraMap A (MvPowerSeries (Fin 2) A)))) = -w →
      algebraMap (MvPowerSeries (Fin 2) A) (WeierstrassCurve.GenK (Fin 2) A) w ≠ 0 →
      ∃ hns : (((W.map (algebraMap A (MvPowerSeries (Fin 2) A)))).toProjective.baseChange (WeierstrassCurve.GenK (Fin 2) A)).toAffine.Nonsingular
          (algebraMap (MvPowerSeries (Fin 2) A) (WeierstrassCurve.GenK (Fin 2) A) z / algebraMap (MvPowerSeries (Fin 2) A) (WeierstrassCurve.GenK (Fin 2) A) w) (-1 / algebraMap (MvPowerSeries (Fin 2) A) (WeierstrassCurve.GenK (Fin 2) A) w),
        ev (WeierstrassCurve.GenK (Fin 2) A) (schemeHomOverComp (Spec.map (CommRingCat.ofHom (algebraMap (MvPowerSeries (Fin 2) A) (WeierstrassCurve.GenK (Fin 2) A)))) htK P) =
          WeierstrassCurve.Affine.Point.some _ _ hns := by
    intro P χ z w hsec hu hv hw
    have hfac : (schemeHomOverComp (Spec.map (CommRingCat.ofHom (algebraMap (MvPowerSeries (Fin 2) A) (WeierstrassCurve.GenK (Fin 2) A)))) htK P).1 =
        Spec.map (CommRingCat.ofHom ((algebraMap (MvPowerSeries (Fin 2) A) (WeierstrassCurve.GenK (Fin 2) A)).comp χ)) ≫ originChartι (W.map (algebraMap A (MvPowerSeries (Fin 2) A))) := by
      show Spec.map (CommRingCat.ofHom (algebraMap (MvPowerSeries (Fin 2) A) (WeierstrassCurve.GenK (Fin 2) A))) ≫ P.1 = _
      rw [hsec, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have hvK : ((algebraMap (MvPowerSeries (Fin 2) A) (WeierstrassCurve.GenK (Fin 2) A)).comp χ) (zOverY (W.map (algebraMap A (MvPowerSeries (Fin 2) A)))) ≠ 0 := by
      rw [RingHom.comp_apply, hv, map_neg, neg_ne_zero]; exact hw
    obtain ⟨ζ, hζ, hζx, hζy⟩ := WeierstrassCurve.DrinfeldGlobal.exists_eq_comp_zChartInclusion_of_eq_comp_originChartInclusion (W.map (algebraMap A (MvPowerSeries (Fin 2) A)))
      _ ((algebraMap (MvPowerSeries (Fin 2) A) (WeierstrassCurve.GenK (Fin 2) A)).comp χ) hfac hvK
    obtain ⟨hns, hevP⟩ := hevc (WeierstrassCurve.GenK (Fin 2) A) _ ζ hζ
    have hx : ζ (xOverZ ((W.map (algebraMap A (MvPowerSeries (Fin 2) A)))).toProjective) = algebraMap (MvPowerSeries (Fin 2) A) (WeierstrassCurve.GenK (Fin 2) A) z / algebraMap (MvPowerSeries (Fin 2) A) (WeierstrassCurve.GenK (Fin 2) A) w := by
      rw [hζx, RingHom.comp_apply, RingHom.comp_apply, hu, hv, map_neg, map_neg, neg_div_neg_eq]
    have hy : ζ (yOverZ ((W.map (algebraMap A (MvPowerSeries (Fin 2) A)))).toProjective) = -1 / algebraMap (MvPowerSeries (Fin 2) A) (WeierstrassCurve.GenK (Fin 2) A) w := by
      rw [hζy, RingHom.comp_apply, hv, map_neg, div_neg, neg_div]
    refine ⟨by rw [← hx, ← hy]; exact hns, ?_⟩
    rw [hevP]
    exact some_eq_some hx hy _ _

  obtain ⟨hsec₁, hz₁J, hw₁J⟩ := h₁
  obtain ⟨hsec₂, hz₂J, hw₂J⟩ := h₂
  have hsc₁ := apply_sc_eq (W.map (algebraMap A (MvPowerSeries (Fin 2) A))) P₁ χ₁ hsec₁
  have hsc₂ := apply_sc_eq (W.map (algebraMap A (MvPowerSeries (Fin 2) A))) P₂ χ₂ hsec₂
  have hu₁ : χ₁ (xOverY (W.map (algebraMap A (MvPowerSeries (Fin 2) A)))) = -MvPowerSeries.X 0 := by
    have : originParam χ₁ = -χ₁ (xOverY (W.map (algebraMap A (MvPowerSeries (Fin 2) A)))) := rfl
    rw [hz₁] at this; linear_combination this
  have hu₂ : χ₂ (xOverY (W.map (algebraMap A (MvPowerSeries (Fin 2) A)))) = -MvPowerSeries.X 1 := by
    have : originParam χ₂ = -χ₂ (xOverY (W.map (algebraMap A (MvPowerSeries (Fin 2) A)))) := rfl
    rw [hz₂] at this; linear_combination this

  have cubic : ∀ (P : Section (W.map (algebraMap A (MvPowerSeries (Fin 2) A)))) (χ : OriginChartRing (W.map (algebraMap A (MvPowerSeries (Fin 2) A))) →+* (MvPowerSeries (Fin 2) A)) (z : (MvPowerSeries (Fin 2) A)),
      IsOriginChartSection P χ → χ (xOverY (W.map (algebraMap A (MvPowerSeries (Fin 2) A)))) = -z → MvPowerSeries.constantCoeff z = 0 →
      originW χ ∈ Ideal.span {(MvPowerSeries.X 0 : (MvPowerSeries (Fin 2) A)), MvPowerSeries.X 1} →
      χ (zOverY (W.map (algebraMap A (MvPowerSeries (Fin 2) A)))) = -(W.fgGenW z) := by
    intro P χ z hsec hu hz hwJ
    have hsc : ∀ t : (MvPowerSeries (Fin 2) A), χ (fromZeroRingHom (projModelGradingCR (W.map (algebraMap A (MvPowerSeries (Fin 2) A)))) _
        (algebraMap (MvPowerSeries (Fin 2) A) ((projModelGradingCR (W.map (algebraMap A (MvPowerSeries (Fin 2) A)))) 0) t)) = algebraMap (MvPowerSeries (Fin 2) A) (MvPowerSeries (Fin 2) A) t := by
      intro t; rw [Algebra.algebraMap_self, RingHom.id_apply]; exact apply_sc_eq (W.map (algebraMap A (MvPowerSeries (Fin 2) A))) P χ hsec t
    have hrel := WeierstrassCurve.DrinfeldGlobal.originChart_rel (W.map (algebraMap A (MvPowerSeries (Fin 2) A))) χ hsc
    simp only [Algebra.algebraMap_self, RingHom.id_apply, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
      WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, hu] at hrel
    have hrel' := neg_fgGenW_rel W z hz
    have hv0 : MvPowerSeries.constantCoeff (χ (zOverY (W.map (algebraMap A (MvPowerSeries (Fin 2) A))))) = 0 := by
      have : originW χ = -χ (zOverY (W.map (algebraMap A (MvPowerSeries (Fin 2) A)))) := rfl
      have h := constantCoeff_eq_zero_of_mem_span_X hwJ
      rw [this, map_neg, neg_eq_zero] at h
      exact h
    have hv0' : MvPowerSeries.constantCoeff (-(W.fgGenW z)) = 0 := by
      rw [map_neg, constantCoeff_fgGenW W z hz, neg_zero]
    have hx0 : MvPowerSeries.constantCoeff (-z) = 0 := by rw [map_neg, hz, neg_zero]
    exact WeierstrassCurve.DrinfeldGlobal.originChart_rel_unique_of_constantCoeff_eq_zero _ _ _ _ _ _ _ _
      hx0 hv0 hv0' hrel hrel'
  have hv₁ := cubic P₁ χ₁ (MvPowerSeries.X 0) hsec₁ hu₁ (MvPowerSeries.constantCoeff_X 0) hw₁J
  have hv₂ := cubic P₂ χ₂ (MvPowerSeries.X 1) hsec₂ hu₂ (MvPowerSeries.constantCoeff_X 1) hw₂J
  obtain ⟨hns₁, hev₁⟩ := read P₁ χ₁ _ _ hsec₁ hu₁ hv₁ hw0
  obtain ⟨hns₂, hev₂⟩ := read P₂ χ₂ _ _ hsec₂ hu₂ hv₂ hw1

  have hrel₃ : (-(W.fgGenW W.formalGroupLawFixed)) +
      algebraMap (MvPowerSeries (Fin 2) A) (MvPowerSeries (Fin 2) A) ((W.map (algebraMap A (MvPowerSeries (Fin 2) A)))).a₁ * (-W.formalGroupLawFixed) * (-(W.fgGenW W.formalGroupLawFixed)) +
      algebraMap (MvPowerSeries (Fin 2) A) (MvPowerSeries (Fin 2) A) ((W.map (algebraMap A (MvPowerSeries (Fin 2) A)))).a₃ * (-(W.fgGenW W.formalGroupLawFixed)) ^ 2 =
      (-W.formalGroupLawFixed) ^ 3 +
      algebraMap (MvPowerSeries (Fin 2) A) (MvPowerSeries (Fin 2) A) ((W.map (algebraMap A (MvPowerSeries (Fin 2) A)))).a₂ * (-W.formalGroupLawFixed) ^ 2 * (-(W.fgGenW W.formalGroupLawFixed)) +
      algebraMap (MvPowerSeries (Fin 2) A) (MvPowerSeries (Fin 2) A) ((W.map (algebraMap A (MvPowerSeries (Fin 2) A)))).a₄ * (-W.formalGroupLawFixed) * (-(W.fgGenW W.formalGroupLawFixed)) ^ 2 +
      algebraMap (MvPowerSeries (Fin 2) A) (MvPowerSeries (Fin 2) A) ((W.map (algebraMap A (MvPowerSeries (Fin 2) A)))).a₆ * (-(W.fgGenW W.formalGroupLawFixed)) ^ 3 := by
    simp only [Algebra.algebraMap_self, RingHom.id_apply, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
      WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆]
    exact neg_fgGenW_rel W W.formalGroupLawFixed hF0
  obtain ⟨χ₃, hsc₃, hχ₃x, hχ₃z⟩ :=
    WeierstrassCurve.DrinfeldGlobal.exists_ringHom_originChartRing_eq (W.map (algebraMap A (MvPowerSeries (Fin 2) A))) (B := (MvPowerSeries (Fin 2) A)) _ _ hrel₃
  have hsc₃' : ∀ t : (MvPowerSeries (Fin 2) A), χ₃ (fromZeroRingHom (projModelGradingCR (W.map (algebraMap A (MvPowerSeries (Fin 2) A)))) _
      (algebraMap (MvPowerSeries (Fin 2) A) ((projModelGradingCR (W.map (algebraMap A (MvPowerSeries (Fin 2) A)))) 0) t)) = t := by
    intro t; have := hsc₃ t; rwa [Algebra.algebraMap_self, RingHom.id_apply] at this
  obtain ⟨hns₃, hev₃⟩ := read (sectionOfChart (W.map (algebraMap A (MvPowerSeries (Fin 2) A))) χ₃ hsc₃') χ₃ _ _
    (isOriginChartSection_sectionOfChart (W.map (algebraMap A (MvPowerSeries (Fin 2) A))) χ₃ hsc₃') hχ₃x hχ₃z hwF

  have hmulK : schemeHomOverComp (Spec.map (CommRingCat.ofHom (algebraMap (MvPowerSeries (Fin 2) A) (WeierstrassCurve.GenK (Fin 2) A)))) htK (G₀.mul (𝟙 _) P₁ P₂) =
      G₀.mul _ (schemeHomOverComp (Spec.map (CommRingCat.ofHom (algebraMap (MvPowerSeries (Fin 2) A) (WeierstrassCurve.GenK (Fin 2) A)))) htK P₁)
        (schemeHomOverComp (Spec.map (CommRingCat.ofHom (algebraMap (MvPowerSeries (Fin 2) A) (WeierstrassCurve.GenK (Fin 2) A)))) htK P₂) :=
    G₀.mul_natural (𝟙 _) _ _ htK P₁ P₂
  have hsum' := hsum.symm
  unfold WeierstrassCurve.genericPoint at hsum'
  have hpt : ev (WeierstrassCurve.GenK (Fin 2) A) (schemeHomOverComp (Spec.map (CommRingCat.ofHom (algebraMap (MvPowerSeries (Fin 2) A) (WeierstrassCurve.GenK (Fin 2) A)))) htK (G₀.mul (𝟙 _) P₁ P₂)) =
      ev (WeierstrassCurve.GenK (Fin 2) A) (schemeHomOverComp (Spec.map (CommRingCat.ofHom (algebraMap (MvPowerSeries (Fin 2) A) (WeierstrassCurve.GenK (Fin 2) A)))) htK
        (sectionOfChart (W.map (algebraMap A (MvPowerSeries (Fin 2) A))) χ₃ hsc₃')) := by
    rw [hmulK, hev.1, hev₁, hev₂, hev₃]
    exact some_add_some_transfer ecurve _ _ _ hns₁ hns₂ hns₃ hsum'
  have heqK := (ev (WeierstrassCurve.GenK (Fin 2) A)).injective hpt
  have heq : G₀.mul (𝟙 _) P₁ P₂ = sectionOfChart (W.map (algebraMap A (MvPowerSeries (Fin 2) A))) χ₃ hsc₃' :=
    WeierstrassCurve.DrinfeldGlobal.section_eq_of_specMap_comp_eq_of_injective (algebraMap (MvPowerSeries (Fin 2) A) (WeierstrassCurve.GenK (Fin 2) A))
      (IsFractionRing.injective (MvPowerSeries (Fin 2) A) (WeierstrassCurve.GenK (Fin 2) A)) (W.map (algebraMap A (MvPowerSeries (Fin 2) A))) _ _ (congrArg Subtype.val heqK)

  have hzF : originParam χ₃ = W.formalGroupLawFixed := by
    show -χ₃ (xOverY (W.map (algebraMap A (MvPowerSeries (Fin 2) A)))) = _; rw [hχ₃x, neg_neg]
  have hwF' : originW χ₃ = W.fgGenW W.formalGroupLawFixed := by
    show -χ₃ (zOverY (W.map (algebraMap A (MvPowerSeries (Fin 2) A)))) = _; rw [hχ₃z, neg_neg]
  refine ⟨χ₃, ?_, hzF⟩
  rw [heq]
  exact ⟨isOriginChartSection_sectionOfChart (W.map (algebraMap A (MvPowerSeries (Fin 2) A))) χ₃ hsc₃',
    hzF ▸ mem_span_X_of_constantCoeff_eq_zero _ hF0,
    hwF' ▸ mem_span_X_of_constantCoeff_eq_zero _ (constantCoeff_fgGenW W _ hF0)⟩

end S_WeierstrassCurve_DrinfeldGlobal_exists_reducesToOrigin_mul_originParam_eq_formalGroupLawFixed
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_reducesToOrigin_mul_originParam_eq_formalGroupLawFixed (solution)
