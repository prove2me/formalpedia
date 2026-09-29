-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.IsOriginChartSection.eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/8dbce7e5-b3de-5af3-9cc8-4640bca8dad7

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_IsOriginChartSection_eq

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal

attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    {T : Type u} [CommRing T] {W : WeierstrassCurve.Projective T} {P : Section W}
    {χ χ' : OriginChartRing W →+* T} (h : IsOriginChartSection P χ) (h' : IsOriginChartSection P χ') :
    χ = χ' := by
  have e : Spec.map (CommRingCat.ofHom χ) ≫ originChartι W = Spec.map (CommRingCat.ofHom χ') ≫ originChartι W :=
    h.symm.trans h'
  rw [cancel_mono] at e
  have e2 := Spec.map_injective e
  exact congrArg CommRingCat.Hom.hom e2

end S_WeierstrassCurve_DrinfeldGlobal_IsOriginChartSection_eq
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_IsOriginChartSection_eq (solution)
