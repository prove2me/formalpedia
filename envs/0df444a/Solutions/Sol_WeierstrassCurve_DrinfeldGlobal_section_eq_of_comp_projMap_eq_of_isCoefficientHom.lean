-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.section_eq_of_comp_projMap_eq_of_isCoefficientHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/b584b3d6-5a09-5cbe-9a91-9e6b3046f986

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isPullback_projMap_of_isCoefficientHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_section_eq_of_comp_projMap_eq_of_isCoefficientHom
p2m_attr_erase "instance" "WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType"
p2m_attr_erase "simp" "WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X"

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal NeronModelInfra

theorem solution
    {T : Type u} [CommRing T] {K : Type u} [Field K]
    (W : WeierstrassCurve T) (f : T →+* K)
    (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f))
    (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f)) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ)
    (hφc : IsCoefficientHom W f φ)
    (s₁ s₂ : Section (W.map f))
    (h : s₁.1 ≫ Proj.map φ hφ = s₂.1 ≫ Proj.map φ hφ) :
    s₁ = s₂ := by
  have hP := WeierstrassCurve.DrinfeldGlobal.isPullback_projMap_of_isCoefficientHom W f φ hφ hφc
  apply Subtype.ext
  exact hP.hom_ext h (by rw [s₁.2, s₂.2])

end S_WeierstrassCurve_DrinfeldGlobal_section_eq_of_comp_projMap_eq_of_isCoefficientHom
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_section_eq_of_comp_projMap_eq_of_isCoefficientHom (solution)
