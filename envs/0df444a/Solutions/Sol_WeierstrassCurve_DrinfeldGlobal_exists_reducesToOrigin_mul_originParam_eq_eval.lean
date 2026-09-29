-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.exists_reducesToOrigin_mul_originParam_eq_eval
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/89375f5a-6b67-5bb3-8f36-9638cb96f13f

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_FormalGroup
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_reducesToOrigin_mul_originParam_eq_formalGroupLawFixed
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_section_reducesToOrigin_originParam_eq_X
import Theorems.Thm_FormalGroup_exists_ringHom_mvPowerSeries_eval_of_mem
import Theorems.Thm_WeierstrassProjModel_exists_relativeGroupLaw_one_eq_zeroSect_isPointsEval_of_isUnit
import Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_exists_isOriginChartSection_iff_one_eq_kwZeroSect
import Theorems.Thm_WeierstrassProjModel_exists_isCoefficientHom
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isPullback_projMap_of_isCoefficientHom
import Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_exists_relativeGroupLaw_comp_eq_of_isPullback
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_one_eq_zeroSect_of_one_comp_projMap_eq_of_isPullback
import Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_mul_eq_of_one_eq_of_isElliptic
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_reducesToOrigin_map_originParam_eq_of_isCoefficientHom
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_section_eq_of_reducesToOrigin_of_originParam_eq
import Theorems.Thm_WeierstrassCurve_formalW_map_and_formalGroupLawFixed_map
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_reducesToOrigin_mul_originParam_eq_eval
p2m_attr_erase "simp" "WeierstrassProjModel.kw_lrThird_substHom_X"

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal IsLocalRing

attribute [local instance] MvPolynomial.gradedAlgebra WeierstrassProjModel.kw_pbac_awayAlgebra

noncomputable section

namespace FormalAddAux

abbrev R₀ : Type := MvPolynomial (Fin 5) ℤ

abbrev W₀ : WeierstrassCurve R₀ := kw_lrSymOC_W₀

theorem W₀_Δ_ne_zero : W₀.Δ ≠ 0 := by
  intro h
  have hmap : (W₀.map (MvPolynomial.eval (![0, 0, 0, -1, 0] : Fin 5 → ℤ))).Δ = 0 := by
    rw [WeierstrassCurve.map_Δ, h, map_zero]
  have hW : W₀.map (MvPolynomial.eval (![0, 0, 0, -1, 0] : Fin 5 → ℤ)) = ⟨0, 0, 0, -1, 0⟩ := by
    ext <;> simp [WeierstrassCurve.map]
  rw [hW] at hmap
  norm_num [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈] at hmap

abbrev Au : Type := Localization.Away W₀.Δ

scoped instance : IsDomain Au :=
  IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors W₀_Δ_ne_zero)

scoped instance : IsNoetherianRing Au :=
  IsLocalization.isNoetherianRing (Submonoid.powers W₀.Δ) Au inferInstance

abbrev Wu : WeierstrassCurve Au := W₀.map (algebraMap R₀ Au)

theorem isUnit_Wu_Δ : IsUnit Wu.Δ := by
  rw [WeierstrassCurve.map_Δ]
  exact IsLocalization.Away.algebraMap_isUnit W₀.Δ

scoped instance : (Wu : WeierstrassCurve.Projective Au).toAffine.IsElliptic := ⟨isUnit_Wu_Δ⟩

theorem exists_classify {R : Type} [CommRing R] (V : WeierstrassCurve R) (hΔ : IsUnit V.Δ) :
    ∃ c : Au →+* R, Wu.map c = V := by
  let φ₀ : R₀ →+* R := MvPolynomial.eval₂Hom (Int.castRingHom R) ![V.a₁, V.a₂, V.a₃, V.a₄, V.a₆]
  have hφ₀ : W₀.map φ₀ = V := kw_lrSymOC_W₀_map V
  have hu : IsUnit (φ₀ W₀.Δ) := by
    rw [← WeierstrassCurve.map_Δ, hφ₀]; exact hΔ
  refine ⟨IsLocalization.Away.lift W₀.Δ hu, ?_⟩
  rw [WeierstrassCurve.map_map, IsLocalization.Away.lift_comp, hφ₀]

abbrev T₀ : Type := MvPowerSeries (Fin 2) Au

abbrev Wz : WeierstrassCurve T₀ := Wu.map (algebraMap Au T₀)

theorem isUnit_Wz_Δ : IsUnit Wz.Δ := by
  rw [WeierstrassCurve.map_Δ]; exact isUnit_Wu_Δ.map _

def castOver {R : Type} [CommRing R] {X Y : Scheme.{0}} {p : X ⟶ Spec (CommRingCat.of R)}
    {t₁ t₂ : Y ⟶ Spec (CommRingCat.of R)} (h : t₁ = t₂) (x : SchemeHomOver t₁ p) : SchemeHomOver t₂ p :=
  ⟨x.1, x.2.trans h⟩

theorem mul_castOver {R : Type} [CommRing R] {X Y : Scheme.{0}} {p : X ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R p) {t₁ t₂ : Y ⟶ Spec (CommRingCat.of R)} (h : t₁ = t₂) (x y : SchemeHomOver t₁ p) :
    G.mul t₂ (castOver h x) (castOver h y) = castOver h (G.mul t₁ x y) := by
  subst h; rfl

theorem reducesToOrigin_mono {T : Type} [CommRing T] {W : WeierstrassCurve.Projective T} {P : Section W}
    {χ : OriginChartRing W →+* T} {I J : Ideal T} (h : ReducesToOrigin P χ I) (hIJ : I ≤ J) :
    ReducesToOrigin P χ J :=
  ⟨h.1, hIJ h.2.1, hIJ h.2.2⟩

end FormalAddAux
p2m_reactivate "P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_reducesToOrigin_mul_originParam_eq_eval.FormalAddAux"

open FormalAddAux in
set_option maxHeartbeats 6400000 in
theorem solution
    {T : Type} [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [IsAdicComplete (maximalIdeal T) T]
    (W : WeierstrassCurve T) [W.IsElliptic]
    (F : FormalGroup T) (hFW : F.toPowerSeries = W.formalGroupLawFixed)
    (G : RelativeGroupLaw T (projModelStrCR W))
    (hGpts : ∃ ev, IsPointsEval W G ev)
    (hGone : ∃ χ : OriginChartRing W →+* T,
      IsOriginChartSection (G.one (𝟙 _)) χ ∧ χ (xOverY W) = 0 ∧ χ (zOverY W) = 0)
    (P₁ P₂ : Section W) (χ₁ χ₂ : OriginChartRing W →+* T)
    (h₁ : ReducesToOrigin P₁ χ₁ (maximalIdeal T)) (h₂ : ReducesToOrigin P₂ χ₂ (maximalIdeal T)) :
    ∃ χ : OriginChartRing W →+* T, ReducesToOrigin (G.mul (𝟙 _) P₁ P₂) χ (maximalIdeal T) ∧
      originParam χ = (letI : WithIdeal T := ⟨maximalIdeal T⟩; F.eval (originParam χ₁) (originParam χ₂)) := by
  classical

  have hΔ : IsUnit W.Δ := W.isUnit_Δ
  obtain ⟨c, hc⟩ := exists_classify W hΔ

  obtain ⟨e, heC, heX0, heX1, heval, -, -⟩ :=
    FormalGroup.exists_ringHom_mvPowerSeries_eval_of_mem c (maximalIdeal T) (originParam χ₁) (originParam χ₂)
      h₁.2.1 h₂.2.1
  have hec : e.comp (algebraMap Au (MvPowerSeries (Fin 2) Au)) = c := RingHom.ext fun a => heC a

  have hWe : Wz.map e = W := by
    rw [Wz, WeierstrassCurve.map_map, hec, hc]
  subst hWe
  haveI hEll : ((Wz.map e : WeierstrassCurve T) : WeierstrassCurve.Projective T).toAffine.IsElliptic := ⟨hΔ⟩

  have hbc : Wu.formalGroup.IsBaseChange c F := by
    show F.toPowerSeries = MvPowerSeries.map c Wu.formalGroup.toPowerSeries
    rw [hFW, WeierstrassCurve.map_map, hec]
    exact (WeierstrassCurve.formalW_map_and_formalGroupLawFixed_map Wu c).2
  have hFeval : (letI : WithIdeal T := ⟨maximalIdeal T⟩; F.eval (originParam χ₁) (originParam χ₂)) =
      e Wu.formalGroupLawFixed := heval Wu.formalGroup F hbc

  obtain ⟨G₀, ev₀, hone₀, hev₀⟩ :=
    WeierstrassProjModel.exists_relativeGroupLaw_one_eq_zeroSect_isPointsEval_of_isUnit Wz isUnit_Wz_Δ
  have hGone₀ : ∃ χ : OriginChartRing Wz →+* T₀,
      IsOriginChartSection (G₀.one (𝟙 _)) χ ∧ χ (xOverY Wz) = 0 ∧ χ (zOverY Wz) = 0 :=
    (WeierstrassProjModel.RelativeGroupLaw.exists_isOriginChartSection_iff_one_eq_kwZeroSect Wz G₀).mpr
      (by rw [hone₀, Category.id_comp])

  obtain ⟨𝒫₁, ψ₁, h𝒫₁, hψ₁⟩ :=
    WeierstrassCurve.DrinfeldGlobal.exists_section_reducesToOrigin_originParam_eq_X Wu (0 : Fin 2)
  obtain ⟨𝒫₂, ψ₂, h𝒫₂, hψ₂⟩ :=
    WeierstrassCurve.DrinfeldGlobal.exists_section_reducesToOrigin_originParam_eq_X Wu (1 : Fin 2)
  obtain ⟨ψ₃, h𝒫₃, hψ₃⟩ :=
    WeierstrassCurve.DrinfeldGlobal.exists_reducesToOrigin_mul_originParam_eq_formalGroupLawFixed Wu G₀ ⟨ev₀, hev₀⟩
      hGone₀ 𝒫₁ 𝒫₂ ψ₁ ψ₂ h𝒫₁ h𝒫₂ hψ₁ hψ₂

  obtain ⟨φe, hφe, hcoef⟩ := WeierstrassProjModel.exists_isCoefficientHom (Wz : WeierstrassCurve.Projective T₀) e
  have hP := WeierstrassCurve.DrinfeldGlobal.isPullback_projMap_of_isCoefficientHom
    (Wz : WeierstrassCurve.Projective T₀) e φe hφe hcoef
  obtain ⟨G', hmul', hone'⟩ :=
    WeierstrassProjModel.RelativeGroupLaw.exists_relativeGroupLaw_comp_eq_of_isPullback e
      (projModelStrCR Wz) (projModelStrCR (Wz.map e)) (Proj.map φe hφe) hP G₀
  have hG'one : ∀ {S : Scheme.{0}} (s : S ⟶ Spec (CommRingCat.of T)),
      (G'.one s).1 = s ≫ (kwZeroSect T (Wz.map e).toAffine).1 := fun {S} s =>
    WeierstrassCurve.DrinfeldGlobal.one_eq_zeroSect_of_one_comp_projMap_eq_of_isPullback
      (Wz : WeierstrassCurve.Projective T₀) e φe hφe hcoef hP G₀ G' (fun {S} s => hone₀ s) hone' s
  have hGz : (G.one (𝟙 _)).1 = (kwZeroSect T (Wz.map e)).1 :=
    (WeierstrassProjModel.RelativeGroupLaw.exists_isOriginChartSection_iff_one_eq_kwZeroSect (Wz.map e) G).mp hGone
  have hGG' : ∀ (x y : Section (Wz.map e)), G.mul (𝟙 _) x y = G'.mul (𝟙 _) x y := fun x y =>
    WeierstrassProjModel.RelativeGroupLaw.mul_eq_of_one_eq_of_isElliptic (Wz.map e) G G'
      (by rw [hGz, hG'one, Category.id_comp]) _ x y

  let pull : Section Wz → Section (Wz.map e) := fun Q =>
    ⟨hP.lift (Spec.map (CommRingCat.ofHom e) ≫ Q.1) (𝟙 _)
        (by rw [Category.assoc, Q.2, Category.comp_id, Category.id_comp]),
      hP.lift_snd _ _ _⟩
  have hpull : ∀ Q : Section Wz, (pull Q).1 ≫ Proj.map φe hφe = Spec.map (CommRingCat.ofHom e) ≫ Q.1 :=
    fun Q => hP.lift_fst _ _ _
  have hJ : (Ideal.span {(MvPowerSeries.X 0 : T₀), MvPowerSeries.X 1}).map e ≤ maximalIdeal T := by
    rw [Ideal.map_le_iff_le_comap, Ideal.span_le]
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · simpa [Ideal.mem_comap, heX0] using h₁.2.1
    · simpa [Ideal.mem_comap, heX1] using h₂.2.1

  obtain ⟨χ₁', hχ₁', hz₁', -⟩ :=
    WeierstrassCurve.DrinfeldGlobal.exists_reducesToOrigin_map_originParam_eq_of_isCoefficientHom Wz e φe hφe hcoef
      𝒫₁ ψ₁ _ h𝒫₁ (pull 𝒫₁) (hpull 𝒫₁)
  obtain ⟨χ₂', hχ₂', hz₂', -⟩ :=
    WeierstrassCurve.DrinfeldGlobal.exists_reducesToOrigin_map_originParam_eq_of_isCoefficientHom Wz e φe hφe hcoef
      𝒫₂ ψ₂ _ h𝒫₂ (pull 𝒫₂) (hpull 𝒫₂)
  obtain ⟨χ₃', hχ₃', hz₃', -⟩ :=
    WeierstrassCurve.DrinfeldGlobal.exists_reducesToOrigin_map_originParam_eq_of_isCoefficientHom Wz e φe hφe hcoef
      (G₀.mul (𝟙 _) 𝒫₁ 𝒫₂) ψ₃ _ h𝒫₃ (pull (G₀.mul (𝟙 _) 𝒫₁ 𝒫₂)) (hpull _)
  have hP₁ : pull 𝒫₁ = P₁ :=
    (WeierstrassCurve.DrinfeldGlobal.section_eq_of_reducesToOrigin_of_originParam_eq (Wz.map e) (pull 𝒫₁) P₁ χ₁' χ₁
      (reducesToOrigin_mono hχ₁' hJ) h₁ (by rw [hz₁', hψ₁, heX0])).1
  have hP₂ : pull 𝒫₂ = P₂ :=
    (WeierstrassCurve.DrinfeldGlobal.section_eq_of_reducesToOrigin_of_originParam_eq (Wz.map e) (pull 𝒫₂) P₂ χ₂' χ₂
      (reducesToOrigin_mono hχ₂' hJ) h₂ (by rw [hz₂', hψ₂, heX1])).1

  have hsum : G.mul (𝟙 _) P₁ P₂ = pull (G₀.mul (𝟙 _) 𝒫₁ 𝒫₂) := by
    rw [hGG', ← hP₁, ← hP₂]
    apply Subtype.ext
    refine hP.hom_ext ?_ ?_
    · have hnat := G₀.mul_natural (𝟙 _) (𝟙 _ ≫ Spec.map (CommRingCat.ofHom e)) (Spec.map (CommRingCat.ofHom e))
        (by rw [Category.comp_id, Category.id_comp]) 𝒫₁ 𝒫₂
      have h1 : ∀ Q : Section Wz,
          (⟨(pull Q).1 ≫ Proj.map φe hφe, by rw [Category.assoc, hP.w, ← Category.assoc, (pull Q).2]⟩ :
            SchemeHomOver (𝟙 _ ≫ Spec.map (CommRingCat.ofHom e)) (projModelStrCR Wz)) =
          WeierstrassProjModel.schemeHomOverComp (Spec.map (CommRingCat.ofHom e))
            (by rw [Category.comp_id, Category.id_comp]) Q :=
        fun Q => Subtype.ext (hpull Q)
      have step : (G₀.mul (𝟙 _ ≫ Spec.map (CommRingCat.ofHom e))
            ⟨(pull 𝒫₁).1 ≫ Proj.map φe hφe, by rw [Category.assoc, hP.w, ← Category.assoc, (pull 𝒫₁).2]⟩
            ⟨(pull 𝒫₂).1 ≫ Proj.map φe hφe, by rw [Category.assoc, hP.w, ← Category.assoc, (pull 𝒫₂).2]⟩).1 =
          Spec.map (CommRingCat.ofHom e) ≫ (G₀.mul (𝟙 _) 𝒫₁ 𝒫₂).1 :=
        (congrArg₂ (fun a b => (G₀.mul (𝟙 _ ≫ Spec.map (CommRingCat.ofHom e)) a b).1) (h1 𝒫₁) (h1 𝒫₂)).trans
          ((congrArg Subtype.val hnat).symm.trans rfl)
      exact (hmul' _ _ _).trans (step.trans (hpull _).symm)
    · rw [(G'.mul _ _ _).2, (pull _).2]
  refine ⟨χ₃', ?_, ?_⟩
  · rw [hsum]; exact reducesToOrigin_mono hχ₃' hJ
  · rw [hz₃', hψ₃, hFeval]

end
end S_WeierstrassCurve_DrinfeldGlobal_exists_reducesToOrigin_mul_originParam_eq_eval
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_reducesToOrigin_mul_originParam_eq_eval (solution)
