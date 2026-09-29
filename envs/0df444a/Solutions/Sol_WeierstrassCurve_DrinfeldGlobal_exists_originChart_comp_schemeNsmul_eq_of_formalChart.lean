-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.exists_originChart_comp_schemeNsmul_eq_of_formalChart
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/908ffaeb-5d64-59e8-a60c-50f62c3b4707

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Theorems.Thm_WeierstrassProjModel_exists_isCoefficientHom
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isPullback_projMap_of_isCoefficientHom
import Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_exists_relativeGroupLaw_comp_eq_of_isPullback
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_isPointsEval_of_mul_comp_projMap_eq_of_isPullback
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_one_eq_zeroSect_of_one_comp_projMap_eq_of_isPullback
import Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_exists_isOriginChartSection_iff_one_eq_kwZeroSect
import Theorems.Thm_WeierstrassCurve_formalW_map_and_formalGroupLawFixed_map
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_ringHom_originChartRing_eq
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_ringHom_originChartRing_ext
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_originW_eq_evalSeries_formalW_originParam_of_isOriginChartSection
import Theorems.Thm_MvPowerSeries_isAdicComplete_maximalIdeal
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_reducesToOrigin_linComb_and_originParam_eq_linCombAdic
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_originChartInclusion_comp_projMap_eq_of_isCoefficientHom
import Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_nsmul_comp_eq_of_mul_comp_eq
import Theorems.Thm_FormalGroup_linCombAdic_map_X_eq_nthSeries
import Theorems.Thm_FormalGroup_evalSeries_map_algebraMap_eq_subst
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_originChart_comp_schemeNsmul_eq_of_formalChart
p2m_attr_erase "instance" "MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid MvFormalGroup.instIsCommAddMv MvFormalGroup.instIsCommOfFormalGroup"
p2m_attr_erase "simp" "FormalGroup.LawIso.mk.sizeOf_spec FormalGroup.LawHom.mk.sizeOf_spec FormalGroup.LawHom.mk.injEq FormalGroup.LawIso.mk.injEq WeierstrassProjModel.kw_lrThird_substHom_X MvFormalGroup.Hom.toPowerSeries_sub MvFormalGroup.linearPartHom_intCast MvFormalGroup.constantCoeff_negSeries MvFormalGroup.toPowerSeries_invHom MvFormalGroup.linearPartHom_neg MvFormalGroup.End.toPowerSeries_sub MvFormalGroup.End.toPowerSeries_neg MvFormalGroup.constantCoeff_invSeries MvFormalGroup.negApprox_zero MvFormalGroup.Hom.toPowerSeries_neg MvFormalGroup.Hom.toPowerSeries_neg' MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast MvFormalGroup.mk.injEq MvFormalGroup.nthSeries_zero MvFormalGroup.Hom.mk.sizeOf_spec MvFormalGroup.Hom.mk.injEq MvFormalGroup.mk.sizeOf_spec MvFormalGroup.e3_one MvFormalGroup.e3_zero MvFormalGroup.e3_two MvFormalGroup.e2_one MvFormalGroup.e2_zero FormalGroup.LawHom.ofMvHom_series MvFormalGroup.e1_apply"
p2m_attr_erase "simp" "FormalGroup.LawHom.toMvHom_toPowerSeries"

set_option autoImplicit false

p2m_open "AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_originChart_comp_schemeNsmul_eq_of_formalChart.WeierstrassCurve.DrinfeldGlobal IsLocalRing HomogeneousLocalization"

attribute [local instance] MvPolynomial.gradedAlgebra

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "toProjective a₃ a₁ map a₄ a₂ a₆ map_id map_injective map_a₆ map_a₁ map_a₄ map_a₂ map_a₃ formalW constantCoeff_formalW formalW_eq formalGroupLawFixed DrinfeldGlobal.isPullback_projMap_of_isCoefficientHom DrinfeldGlobal.exists_isPointsEval_of_mul_comp_projMap_eq_of_isPullback DrinfeldGlobal.one_eq_zeroSect_of_one_comp_projMap_eq_of_isPullback formalW_map_and_formalGroupLawFixed_map DrinfeldGlobal.exists_ringHom_originChartRing_eq DrinfeldGlobal.ringHom_originChartRing_ext DrinfeldGlobal.originW_eq_evalSeries_formalW_originParam_of_isOriginChartSection DrinfeldGlobal.exists_reducesToOrigin_linComb_and_originParam_eq_linCombAdic DrinfeldGlobal.exists_originChartInclusion_comp_projMap_eq_of_isCoefficientHom"
namespace DrinfeldGlobal
p2m_export "WeierstrassCurve.DrinfeldGlobal" "base Section linComb OriginChartRing originChartι xOverY zOverY IsOriginChartSection originParam originW ReducesToOrigin isPullback_projMap_of_isCoefficientHom exists_isPointsEval_of_mul_comp_projMap_eq_of_isPullback one_eq_zeroSect_of_one_comp_projMap_eq_of_isPullback exists_ringHom_originChartRing_eq ringHom_originChartRing_ext originW_eq_evalSeries_formalW_originParam_of_isOriginChartSection exists_reducesToOrigin_linComb_and_originParam_eq_linCombAdic exists_originChartInclusion_comp_projMap_eq_of_isCoefficientHom"
namespace FormalNsmul
p2m_open "WeierstrassCurve.DrinfeldGlobal WeierstrassCurve"

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

theorem one_val {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f) {S : Scheme.{0}} (t : S ⟶ Spec (CommRingCat.of R)) :
    (G.one t).1 = t ≫ (G.one (𝟙 _)).1 := by
  rw [← G.one_natural (𝟙 _) t t (Category.comp_id t)]
  rfl

theorem nsmul_val_congr {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f) {S : Scheme.{0}} :
    ∀ {t t' : S ⟶ Spec (CommRingCat.of R)} (e : t = t') (n : ℕ) (x : SchemeHomOver t f),
      (G.nsmul t n x).1 = (G.nsmul t' n ⟨x.1, e ▸ x.2⟩).1 := by
  rintro t _ rfl n x; rfl

end WeierstrassCurve.DrinfeldGlobal.FormalNsmul

open WeierstrassCurve.DrinfeldGlobal.FormalNsmul in
set_option maxHeartbeats 6400000 in
theorem solution
    {T : Type} [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [IsAdicComplete (maximalIdeal T) T]
    (W : WeierstrassCurve T) [W.IsElliptic]
    (F : FormalGroup T) (hFW : F.toPowerSeries = W.formalGroupLawFixed)
    (G : RelativeGroupLaw T (projModelStrCR W))
    (hGpts : ∃ ev, IsPointsEval W G ev)
    (hGone : ∃ χ : OriginChartRing W →+* T,
      IsOriginChartSection (G.one (𝟙 _)) χ ∧ χ (xOverY W) = 0 ∧ χ (zOverY W) = 0)
    (q : ℕ)
    (Φ : OriginChartRing W →+* PowerSeries T)
    (hΦsc : ∀ t : T, Φ (fromZeroRingHom (projModelGradingCR W) _ (algebraMap T ((projModelGradingCR W) 0) t)) =
      PowerSeries.C t)
    (hΦx : Φ (xOverY W) = - PowerSeries.X) (hΦz : Φ (zOverY W) = - W.formalW) :
    ∃ χ : OriginChartRing W →+* PowerSeries T,
      (∀ t : T, χ (fromZeroRingHom (projModelGradingCR W) _ (algebraMap T ((projModelGradingCR W) 0) t)) =
        PowerSeries.C t) ∧
      Spec.map (CommRingCat.ofHom Φ) ≫ originChartι W ≫ G.schemeNsmul q =
        Spec.map (CommRingCat.ofHom χ) ≫ originChartι W ∧
      χ (xOverY W) = - F.nthSeries q ∧
      χ (zOverY W) = - PowerSeries.subst (F.nthSeries q) W.formalW := by
  classical

  haveI : IsAdicComplete (maximalIdeal (PowerSeries T)) (PowerSeries T) :=
    MvPowerSeries.isAdicComplete_maximalIdeal (σ := Unit) (R := T)
  have hXm : (PowerSeries.X : (PowerSeries T)) ∈ maximalIdeal (PowerSeries T) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff,
      PowerSeries.constantCoeff_X]
    exact not_isUnit_zero
  have hwm : W.formalW ∈ maximalIdeal (PowerSeries T) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff,
      W.constantCoeff_formalW]
    exact not_isUnit_zero

  obtain ⟨φ, hφ, hcoef⟩ := WeierstrassProjModel.exists_isCoefficientHom W.toProjective (algebraMap T (PowerSeries T))
  have hK2 := WeierstrassCurve.DrinfeldGlobal.isPullback_projMap_of_isCoefficientHom W.toProjective
    (algebraMap T (PowerSeries T)) φ hφ hcoef
  obtain ⟨G', hmul, hone⟩ := WeierstrassProjModel.RelativeGroupLaw.exists_relativeGroupLaw_comp_eq_of_isPullback
    (algebraMap T (PowerSeries T)) (projModelStrCR W.toProjective) (projModelStrCR (W.map (algebraMap T (PowerSeries T)))) (Proj.map φ hφ) hK2 G
  have hG1 : (G.one (𝟙 _)).1 = (kwZeroSect T W).1 :=
    (WeierstrassProjModel.RelativeGroupLaw.exists_isOriginChartSection_iff_one_eq_kwZeroSect W G).mp hGone
  have hG : ∀ {S : Scheme.{0}} (s : S ⟶ Spec (CommRingCat.of T)), (G.one s).1 = s ≫ (kwZeroSect T W).1 := by
    intro S s; rw [one_val, hG1]
  have hG' : ∀ {S : Scheme.{0}} (s : S ⟶ Spec (CommRingCat.of (PowerSeries T))),
      (G'.one s).1 = s ≫ (kwZeroSect (PowerSeries T) (W.map (algebraMap T (PowerSeries T)))).1 :=
    fun s ↦ WeierstrassCurve.DrinfeldGlobal.one_eq_zeroSect_of_one_comp_projMap_eq_of_isPullback W.toProjective
      (algebraMap T (PowerSeries T)) φ hφ hcoef hK2 G G' hG hone s
  have hGone' : ∃ χ : OriginChartRing (W.map (algebraMap T (PowerSeries T))) →+* (PowerSeries T),
      IsOriginChartSection (G'.one (𝟙 _)) χ ∧ χ (xOverY (W.map (algebraMap T (PowerSeries T)))) = 0 ∧ χ (zOverY (W.map (algebraMap T (PowerSeries T)))) = 0 :=
    (WeierstrassProjModel.RelativeGroupLaw.exists_isOriginChartSection_iff_one_eq_kwZeroSect (W.map (algebraMap T (PowerSeries T))) G').mpr
      (by rw [hG', Category.id_comp])
  obtain ⟨ev, hev⟩ := hGpts
  have hGpts' : ∃ ev', IsPointsEval (W.map (algebraMap T (PowerSeries T))) G' ev' :=
    WeierstrassCurve.DrinfeldGlobal.exists_isPointsEval_of_mul_comp_projMap_eq_of_isPullback W.toProjective
      (algebraMap T (PowerSeries T)) φ hφ hcoef hK2 G G' hmul ev hev

  have hFW' : (F.map (algebraMap T (PowerSeries T))).toPowerSeries = ((W.map (algebraMap T (PowerSeries T)))).formalGroupLawFixed := by
    rw [(WeierstrassCurve.formalW_map_and_formalGroupLawFixed_map W (algebraMap T (PowerSeries T))).2, ← hFW]; rfl

  have hrel : (-W.formalW) + algebraMap (PowerSeries T) (PowerSeries T) ((W.map (algebraMap T (PowerSeries T)))).a₁ * (-PowerSeries.X) * (-W.formalW) +
      algebraMap (PowerSeries T) (PowerSeries T) ((W.map (algebraMap T (PowerSeries T)))).a₃ * (-W.formalW) ^ 2 =
      (-PowerSeries.X) ^ 3 + algebraMap (PowerSeries T) (PowerSeries T) ((W.map (algebraMap T (PowerSeries T)))).a₂ * (-PowerSeries.X) ^ 2 * (-W.formalW) +
      algebraMap (PowerSeries T) (PowerSeries T) ((W.map (algebraMap T (PowerSeries T)))).a₄ * (-PowerSeries.X) * (-W.formalW) ^ 2 +
      algebraMap (PowerSeries T) (PowerSeries T) ((W.map (algebraMap T (PowerSeries T)))).a₆ * (-W.formalW) ^ 3 := by
    simp only [Algebra.algebraMap_self, RingHom.id_apply, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
      WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆]
    have h := W.formalW_eq
    have hC : ∀ a : T, (PowerSeries.C a : (PowerSeries T)) = algebraMap T (PowerSeries T) a := fun a ↦ rfl
    simp only [hC] at h
    linear_combination (-1 : (PowerSeries T)) * h
  obtain ⟨χ₀', hsc₀, hχ₀x, hχ₀z⟩ :=
    WeierstrassCurve.DrinfeldGlobal.exists_ringHom_originChartRing_eq (W.map (algebraMap T (PowerSeries T))) (B := (PowerSeries T)) _ _ hrel
  have hsc₀' : ∀ t : (PowerSeries T), χ₀' (fromZeroRingHom (projModelGradingCR (W.map (algebraMap T (PowerSeries T)))) _
      (algebraMap (PowerSeries T) ((projModelGradingCR (W.map (algebraMap T (PowerSeries T)))) 0) t)) = t := by
    intro t; have := hsc₀ t; rwa [Algebra.algebraMap_self, RingHom.id_apply] at this
  let Q' : Section (W.map (algebraMap T (PowerSeries T))) := sectionOfChart (W.map (algebraMap T (PowerSeries T))) χ₀' hsc₀'
  have hQ'sec : IsOriginChartSection Q' χ₀' := rfl
  have hQ'z : originParam χ₀' = PowerSeries.X := by
    show -χ₀' (xOverY (W.map (algebraMap T (PowerSeries T)))) = _; rw [hχ₀x, neg_neg]
  have hQ'w : originW χ₀' = W.formalW := by
    show -χ₀' (zOverY (W.map (algebraMap T (PowerSeries T)))) = _; rw [hχ₀z, neg_neg]
  have hred : ReducesToOrigin Q' χ₀' (maximalIdeal (PowerSeries T)) := ⟨hQ'sec, hQ'z ▸ hXm, hQ'w ▸ hwm⟩

  obtain ⟨χ₀, hχ₀, hχ₀sc, hχ₀u, hχ₀v⟩ :=
    WeierstrassCurve.DrinfeldGlobal.exists_originChartInclusion_comp_projMap_eq_of_isCoefficientHom W.toProjective
      (algebraMap T (PowerSeries T)) φ hφ hcoef χ₀'
  have hχ₀Φ : χ₀ = Φ := by
    apply WeierstrassCurve.DrinfeldGlobal.ringHom_originChartRing_ext W χ₀ Φ
    · intro t; rw [hχ₀sc, hsc₀, hΦsc]; rfl
    · rw [hχ₀u, hχ₀x, hΦx]
    · rw [hχ₀v, hχ₀z, hΦz]
  have hγ : Spec.map (CommRingCat.ofHom Φ) ≫ originChartι W = Q'.1 ≫ Proj.map φ hφ := by
    rw [← hχ₀Φ, ← hχ₀]; rfl

  have hψ : (Q'.1 ≫ Proj.map φ hφ) ≫ projModelStrCR W.toProjective = Spec.map (CommRingCat.ofHom (algebraMap T (PowerSeries T))) := by
    rw [Category.assoc, hK2.w, ← Category.assoc, Q'.2, Category.id_comp]
  have hnat := G.nsmul_natural (projModelStrCR W.toProjective) (Spec.map (CommRingCat.ofHom (algebraMap T (PowerSeries T))))
    (Q'.1 ≫ Proj.map φ hφ) hψ q RelativeGroupLaw.idPoint
  have hL : Spec.map (CommRingCat.ofHom Φ) ≫ originChartι W ≫ G.schemeNsmul q =
      (G.nsmul (Spec.map (CommRingCat.ofHom (algebraMap T (PowerSeries T)))) q ⟨Q'.1 ≫ Proj.map φ hφ, hψ⟩).1 := by
    rw [← Category.assoc, hγ]
    have h1 := congrArg Subtype.val hnat
    simp only [schemeHomOverComp_coe] at h1
    have h2 : schemeHomOverComp (Q'.1 ≫ Proj.map φ hφ) hψ RelativeGroupLaw.idPoint =
        (⟨Q'.1 ≫ Proj.map φ hφ, hψ⟩ : SchemeHomOver _ (projModelStrCR W.toProjective)) :=
      Subtype.ext (Category.comp_id _)
    rw [h2] at h1
    exact h1
  have hN1b := WeierstrassProjModel.RelativeGroupLaw.nsmul_comp_eq_of_mul_comp_eq (algebraMap T (PowerSeries T))
    (projModelStrCR W.toProjective) (projModelStrCR (W.map (algebraMap T (PowerSeries T)))) (Proj.map φ hφ) hK2 G G' hmul hone (𝟙 _) q Q'
  have hup : Spec.map (CommRingCat.ofHom Φ) ≫ originChartι W ≫ G.schemeNsmul q = (G'.nsmul (𝟙 _) q Q').1 ≫ Proj.map φ hφ := by
    rw [hL, hN1b]
    exact nsmul_val_congr G (Category.id_comp _).symm q ⟨Q'.1 ≫ Proj.map φ hφ, hψ⟩

  obtain ⟨χq', hredq, hzq⟩ :=
    WeierstrassCurve.DrinfeldGlobal.exists_reducesToOrigin_linComb_and_originParam_eq_linCombAdic (W.map (algebraMap T (PowerSeries T)))
      (F.map (algebraMap T (PowerSeries T))) hFW' G' hGpts' hGone' Q' Q' χ₀' χ₀' hred hred q 0
  have hlin : linComb G' Q' Q' q 0 = G'.nsmul (𝟙 _) q Q' := by
    show G'.mul _ (G'.nsmul _ q Q') (G'.one _) = _
    exact G'.mul_one _ _
  rw [hlin] at hredq
  rw [hQ'z, FormalGroup.linCombAdic_map_X_eq_nthSeries F q PowerSeries.X hXm] at hzq
  obtain ⟨hsecq, hzqm, hwqm⟩ := hredq
  have hwq : originW χq' = PowerSeries.subst (F.nthSeries q) W.formalW := by
    rw [WeierstrassCurve.DrinfeldGlobal.originW_eq_evalSeries_formalW_originParam_of_isOriginChartSection (W.map (algebraMap T (PowerSeries T)))
      (G'.nsmul (𝟙 _) q Q') χq' hsecq hzqm hwqm, hzq,
      (WeierstrassCurve.formalW_map_and_formalGroupLawFixed_map W (algebraMap T (PowerSeries T))).1]
    exact FormalGroup.evalSeries_map_algebraMap_eq_subst W.formalW (F.nthSeries q) (F.constantCoeff_nthSeries q)

  obtain ⟨χq, hχq, hχqsc, hχqu, hχqv⟩ :=
    WeierstrassCurve.DrinfeldGlobal.exists_originChartInclusion_comp_projMap_eq_of_isCoefficientHom W.toProjective
      (algebraMap T (PowerSeries T)) φ hφ hcoef χq'
  have hscq' := apply_sc_eq (W.map (algebraMap T (PowerSeries T))) _ χq' hsecq
  refine ⟨χq, ?_, ?_, ?_, ?_⟩
  · intro t; rw [hχqsc, hscq']; rfl
  · rw [hup, hsecq, Category.assoc, hχq]
  · rw [hχqu]; have : originParam χq' = -χq' (xOverY (W.map (algebraMap T (PowerSeries T)))) := rfl; rw [hzq] at this; linear_combination this
  · rw [hχqv]; have : originW χq' = -χq' (zOverY (W.map (algebraMap T (PowerSeries T)))) := rfl; rw [hwq] at this; linear_combination this

end S_WeierstrassCurve_DrinfeldGlobal_exists_originChart_comp_schemeNsmul_eq_of_formalChart
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_originChart_comp_schemeNsmul_eq_of_formalChart (solution)
