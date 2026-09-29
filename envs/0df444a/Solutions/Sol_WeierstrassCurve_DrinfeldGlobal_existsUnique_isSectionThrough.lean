-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.existsUnique_isSectionThrough
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/9c15b821-0c2d-5079-9b7a-bccbd358e0b3

import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_PointChart
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_equation_iff_exists_isSectionThrough_and_eq_iff_of_isSectionThrough
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_existsUnique_isSectionThrough
p2m_attr_erase "instance" "WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType"
p2m_attr_erase "simp" "WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X"

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal

attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    {T : Type u} [CommRing T] (W : WeierstrassCurve.Projective T) (x y : T)
    (hxy : W.toAffine.Equation x y) :
    ∃! S : Section W, IsSectionThrough S x y := by
  obtain ⟨h1, h2⟩ :=
    WeierstrassCurve.DrinfeldGlobal.equation_iff_exists_isSectionThrough_and_eq_iff_of_isSectionThrough W
  obtain ⟨S, hS⟩ := (h1 x y).mp hxy
  exact ⟨S, hS, fun S' hS' => (h2 S' S x y x y hS' hS).mpr ⟨rfl, rfl⟩⟩

end S_WeierstrassCurve_DrinfeldGlobal_existsUnique_isSectionThrough
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_existsUnique_isSectionThrough (solution)
