-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.exists_groupLaws_levelTransport_isChordTangent_isOriginIdentity_isSectionTransport
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/c90707c8-02da-51bd-b245-46d929ac9f32

import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_groupLaws_isChordTangent_isOriginIdentity_one_eq_zeroSect
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_levelTransport_isSectionTransport
import Theorems.Thm_WeierstrassProjModel_exists_isVariableChangeHom_isIso_projMap
import Theorems.Thm_WeierstrassProjModel_exists_isCoefficientHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_groupLaws_levelTransport_isChordTangent_isOriginIdentity_isSectionTransport
p2m_attr_erase "simp" "WeierstrassProjModel.kw_lrThird_substHom_X"

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal

attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    (A : Type) [CommRing A] (q : ℕ) :
    ∃ (𝒢 : GroupLaws A) (𝒯 : LevelTransport A 𝒢 q),
      𝒢.IsChordTangent ∧ 𝒢.IsOriginIdentity ∧ 𝒯.IsSectionTransport ∧
      (∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve.Projective T) (C : WeierstrassCurve.VariableChange T),
        ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
          (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤
            (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
          IsVariableChangeHom W C φ) ∧
      (∀ (T T' : Type) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
        (W : WeierstrassCurve.Projective T),
        ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f.toRingHom))
          (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f.toRingHom)) ≤
            (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
          IsCoefficientHom W f.toRingHom φ) := by
  obtain ⟨𝒢, hCT, hOI, -⟩ :=
    WeierstrassCurve.DrinfeldGlobal.exists_groupLaws_isChordTangent_isOriginIdentity_one_eq_zeroSect A
  obtain ⟨𝒯, h𝒯⟩ :=
    WeierstrassCurve.DrinfeldGlobal.exists_levelTransport_isSectionTransport A q 𝒢 hCT hOI
  refine ⟨𝒢, 𝒯, hCT, hOI, h𝒯, ?_, ?_⟩
  · intro T _ _ W C
    obtain ⟨φ, hφ, hvc, -, -⟩ := WeierstrassProjModel.exists_isVariableChangeHom_isIso_projMap W C
    exact ⟨φ, hφ, hvc⟩
  · intro T T' _ _ _ _ f W
    exact WeierstrassProjModel.exists_isCoefficientHom W f.toRingHom

end S_WeierstrassCurve_DrinfeldGlobal_exists_groupLaws_levelTransport_isChordTangent_isOriginIdentity_isSectionTransport
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_groupLaws_levelTransport_isChordTangent_isOriginIdentity_isSectionTransport (solution)
