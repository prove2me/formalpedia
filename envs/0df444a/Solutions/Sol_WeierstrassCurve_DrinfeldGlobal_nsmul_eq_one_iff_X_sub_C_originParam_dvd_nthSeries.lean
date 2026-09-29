-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.nsmul_eq_one_iff_X_sub_C_originParam_dvd_nthSeries
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/7790b416-9508-5334-a542-7c48995e9c2b

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_FormalGroup
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_reducesToOrigin_mul_originParam_eq_eval
import Theorems.Thm_FormalGroup_exists_ringHom_evalSeries_eq
import Theorems.Thm_FormalGroup_ker_evalSeries_eq_span
import Theorems.Thm_FormalGroup_evalSeries_nthSeries
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_section_eq_of_reducesToOrigin_of_originParam_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_nsmul_eq_one_iff_X_sub_C_originParam_dvd_nthSeries
p2m_attr_erase "instance" "WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType"
p2m_attr_erase "simp" "FormalGroup.LawIso.mk.sizeOf_spec FormalGroup.LawHom.mk.sizeOf_spec FormalGroup.LawHom.mk.injEq FormalGroup.LawIso.mk.injEq WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X WeierstrassProjModel.kw_lrThird_substHom_X WeierstrassCurve.DrinfeldGlobal.LevelTransport.mk.injEq WeierstrassCurve.DrinfeldGlobal.LevelTransport.mk.sizeOf_spec"

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal IsLocalRing

attribute [local instance] MvPolynomial.gradedAlgebra

namespace KiAux

theorem chart_unique {T : Type} [CommRing T] {W : WeierstrassCurve T} (P : Section W)
    (χ χ' : OriginChartRing W →+* T) (h : IsOriginChartSection P χ) (h' : IsOriginChartSection P χ') : χ = χ' := by
  have e : Spec.map (CommRingCat.ofHom χ) ≫ originChartι W = Spec.map (CommRingCat.ofHom χ') ≫ originChartι W := by
    rw [← h, ← h']
  have e2 : Spec.map (CommRingCat.ofHom χ) = Spec.map (CommRingCat.ofHom χ') := by
    exact (cancel_mono (originChartι W)).mp e
  have e3 : CommRingCat.ofHom χ = CommRingCat.ofHom χ' := Spec.map_injective e2
  exact congrArg (fun f => f.hom) e3

end KiAux

theorem solution
    {T : Type} [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [IsAdicComplete (maximalIdeal T) T]
    (W : WeierstrassCurve T) [W.IsElliptic]
    (F : FormalGroup T) (hFW : F.toPowerSeries = W.formalGroupLawFixed)
    (G : RelativeGroupLaw T (projModelStrCR W))
    (hGpts : ∃ ev, IsPointsEval W G ev)
    (hGone : ∃ χ : OriginChartRing W →+* T,
      IsOriginChartSection (G.one (𝟙 _)) χ ∧ χ (xOverY W) = 0 ∧ χ (zOverY W) = 0)
    (q : ℕ) (P : Section W) (χP : OriginChartRing W →+* T) (hP : ReducesToOrigin P χP (maximalIdeal T)) :
    G.nsmul (𝟙 _) q P = G.one (𝟙 _) ↔
      (PowerSeries.X - PowerSeries.C (originParam χP)) ∣ F.nthSeries q := by
  classical
  obtain ⟨χ₀, hχ₀, hx₀, hz₀⟩ := hGone
  have hO : ReducesToOrigin (G.one (𝟙 _)) χ₀ (maximalIdeal T) := by
    refine ⟨hχ₀, ?_, ?_⟩
    · simp [originParam, hx₀]
    · simp [originW, hz₀]
  have hO0 : originParam χ₀ = 0 := by simp [originParam, hx₀]
  set z : T := originParam χP with hzdef
  have hz : z ∈ maximalIdeal T := hP.2.1

  have step : ∀ n : ℕ, ∃ χ : OriginChartRing W →+* T, ReducesToOrigin (G.nsmul (𝟙 _) n P) χ (maximalIdeal T) ∧
      originParam χ = (letI : WithIdeal T := ⟨maximalIdeal T⟩; F.evalNSMul n z) := by
    intro n
    induction n with
    | zero => exact ⟨χ₀, by simpa using hO, by simp [hO0]⟩
    | succ n ih =>
      obtain ⟨χn, hχn, hpn⟩ := ih
      obtain ⟨χ, hχ, hp⟩ := WeierstrassCurve.DrinfeldGlobal.exists_reducesToOrigin_mul_originParam_eq_eval
        W F hFW G hGpts ⟨χ₀, hχ₀, hx₀, hz₀⟩ (G.nsmul (𝟙 _) n P) P χn χP hχn hP
      refine ⟨χ, by simpa [RelativeGroupLaw.nsmul_succ] using hχ, ?_⟩
      rw [hp, hpn]
      rfl
  obtain ⟨χq, hχq, hpq⟩ := step q

  letI wI : WithIdeal T := ⟨maximalIdeal T⟩
  have hI : IsAdic (maximalIdeal T) := rfl
  obtain ⟨hcs, ht2⟩ := hI.isAdicComplete_iff.mp (inferInstance : IsAdicComplete (maximalIdeal T) T)
  have hzn : IsTopologicallyNilpotent z := WithIdeal.isTopologicallyNilpotent_of_mem hz
  have hB : FormalGroup.evalSeries (F.nthSeries q) z = F.evalNSMul q z :=
    FormalGroup.evalSeries_nthSeries F hzn q
  obtain ⟨e, he, -⟩ := FormalGroup.exists_ringHom_evalSeries_eq (maximalIdeal T) z hz
  have hker := FormalGroup.ker_evalSeries_eq_span z hz e he
  have hpar : originParam χq = e (F.nthSeries q) := by
    rw [hpq, ← hB, ← he]

  constructor
  · intro h
    have hsec : IsOriginChartSection (G.one (𝟙 _)) χq := by simpa [h] using hχq.1
    have hχeq : χq = χ₀ := KiAux.chart_unique _ χq χ₀ hsec hχ₀
    have h0 : e (F.nthSeries q) = 0 := by rw [← hpar, hχeq, hO0]
    have hmem : F.nthSeries q ∈ RingHom.ker e := h0
    rw [hker, Ideal.mem_span_singleton] at hmem
    exact hmem
  · intro hdvd
    have hmem : F.nthSeries q ∈ RingHom.ker e := by
      rw [hker, Ideal.mem_span_singleton]; exact hdvd
    have h0 : originParam χq = 0 := by rw [hpar]; exact hmem
    exact (WeierstrassCurve.DrinfeldGlobal.section_eq_of_reducesToOrigin_of_originParam_eq W _ _ χq χ₀ hχq hO
      (h0.trans hO0.symm)).1

end S_WeierstrassCurve_DrinfeldGlobal_nsmul_eq_one_iff_X_sub_C_originParam_dvd_nthSeries
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_nsmul_eq_one_iff_X_sub_C_originParam_dvd_nthSeries (solution)
