-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.exists_reducesToOrigin_linComb_and_originParam_eq_linCombAdic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/456f88ec-673f-517a-bdee-ba1aaf9316ed

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_FormalGroup
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_reducesToOrigin_mul_originParam_eq_eval
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_reducesToOrigin_linComb_and_originParam_eq_linCombAdic
p2m_attr_erase "instance" "WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType"
p2m_attr_erase "simp" "FormalGroup.LawIso.mk.sizeOf_spec FormalGroup.LawHom.mk.sizeOf_spec FormalGroup.LawHom.mk.injEq FormalGroup.LawIso.mk.injEq WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X WeierstrassProjModel.kw_lrThird_substHom_X WeierstrassCurve.DrinfeldGlobal.LevelTransport.mk.injEq WeierstrassCurve.DrinfeldGlobal.LevelTransport.mk.sizeOf_spec"

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal IsLocalRing

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 3200000 in
theorem solution
    {T : Type} [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [IsAdicComplete (maximalIdeal T) T]
    (W : WeierstrassCurve T) [W.IsElliptic]
    (F : FormalGroup T) (hFW : F.toPowerSeries = W.formalGroupLawFixed)
    (G : RelativeGroupLaw T (projModelStrCR W))
    (hGpts : ∃ ev, IsPointsEval W G ev)
    (hGone : ∃ χ : OriginChartRing W →+* T,
      IsOriginChartSection (G.one (𝟙 _)) χ ∧ χ (xOverY W) = 0 ∧ χ (zOverY W) = 0)
    (P Q : Section W) (χP χQ : OriginChartRing W →+* T)
    (hP : ReducesToOrigin P χP (maximalIdeal T)) (hQ : ReducesToOrigin Q χQ (maximalIdeal T)) (a b : ℕ) :
    ∃ χ : OriginChartRing W →+* T, ReducesToOrigin (linComb G P Q a b) χ (maximalIdeal T) ∧
      originParam χ = F.linCombAdic (maximalIdeal T) (originParam χP) (originParam χQ) a b := by
  obtain ⟨χ₀, hχ₀, hx0, hz0⟩ := id hGone
  have hO : ReducesToOrigin (G.one (𝟙 _)) χ₀ (maximalIdeal T) := by
    refine ⟨hχ₀, ?_, ?_⟩
    · simp [originParam, hx0]
    · simp [originW, hz0]
  have hO0 : originParam χ₀ = 0 := by simp [originParam, hx0]

  have hns : ∀ (R : Section W) (χR : OriginChartRing W →+* T), ReducesToOrigin R χR (maximalIdeal T) →
      ∀ n : ℕ, ∃ χ : OriginChartRing W →+* T, ReducesToOrigin (G.nsmul (𝟙 _) n R) χ (maximalIdeal T) ∧
        originParam χ = (letI : WithIdeal T := ⟨maximalIdeal T⟩; F.evalNSMul n (originParam χR)) := by
    intro R χR hR n
    induction n with
    | zero => exact ⟨χ₀, by simpa using hO, by rw [hO0]; rfl⟩
    | succ n ih =>
      obtain ⟨χn, hn, hzn⟩ := ih
      obtain ⟨χ, h, hz⟩ :=
        WeierstrassCurve.DrinfeldGlobal.exists_reducesToOrigin_mul_originParam_eq_eval W F hFW G hGpts hGone
          (G.nsmul (𝟙 _) n R) R χn χR hn hR
      refine ⟨χ, by simpa [RelativeGroupLaw.nsmul_succ] using h, ?_⟩
      rw [hz, hzn]
      rfl
  obtain ⟨χa, ha, hza⟩ := hns P χP hP a
  obtain ⟨χb, hb, hzb⟩ := hns Q χQ hQ b
  obtain ⟨χ, h, hz⟩ :=
    WeierstrassCurve.DrinfeldGlobal.exists_reducesToOrigin_mul_originParam_eq_eval W F hFW G hGpts hGone
      (G.nsmul (𝟙 _) a P) (G.nsmul (𝟙 _) b Q) χa χb ha hb
  refine ⟨χ, h, ?_⟩
  rw [hz, hza, hzb]
  rfl

end S_WeierstrassCurve_DrinfeldGlobal_exists_reducesToOrigin_linComb_and_originParam_eq_linCombAdic
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_reducesToOrigin_linComb_and_originParam_eq_linCombAdic (solution)
