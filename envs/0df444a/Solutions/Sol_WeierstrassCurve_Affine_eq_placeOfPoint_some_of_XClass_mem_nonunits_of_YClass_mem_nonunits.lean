-- Prove2me | solution 1 for WeierstrassCurve.Affine.eq_placeOfPoint_some_of_XClass_mem_nonunits_of_YClass_mem_nonunits
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/27bec31f-bafa-5013-a176-befc6fbbfbc9

import Mathlib
import Definitions.Def_WeierstrassCurve_GenusOnePlaceGateCentred
import Theorems.Thm_AlgebraicCurve_Place_eq_ofHeightOneSpectrum_of_XClass_mem_nonunits_of_YClass_mem_nonunits
import Theorems.Thm_WeierstrassCurve_Affine_placeOfPoint_some_eq_ofHeightOneSpectrum
import Theorems.Thm_P2M_Dup_WeierstrassCurve_Affine_CoordinateRing_XYIdeal_isMaximal
import Theorems.Thm_WeierstrassCurve_Affine_CoordinateRing_XYIdeal_ne_bot
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_Affine_eq_placeOfPoint_some_of_XClass_mem_nonunits_of_YClass_mem_nonunits
p2m_attr_erase "instance" "WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal"

set_option autoImplicit false

open AlgebraicCurve WeierstrassCurve WeierstrassCurve.Affine

universe u

theorem solution
    {F : Type u} [Field F] [DecidableEq F] {W : WeierstrassCurve.Affine F}
    [GenusOnePlaceGate W] [GenusOnePlaceGate.IsCentred W] [IsDedekindDomain W.CoordinateRing]
    {x y : F} (h : W.Nonsingular x y) (v : AlgebraicCurve.Place F W.FunctionField)
    (hX : algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.XClass W x)
      ∈ v.toValuationSubring.nonunits)
    (hY : algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.YClass W (Polynomial.C y))
      ∈ v.toValuationSubring.nonunits) :
    v = placeOfPoint (Point.some x y h) := by
  let w : IsDedekindDomain.HeightOneSpectrum W.CoordinateRing :=
    ⟨CoordinateRing.XYIdeal W x (Polynomial.C y), (CoordinateRing.XYIdeal_isMaximal h.left).isPrime,
      CoordinateRing.XYIdeal_ne_bot x (Polynomial.C y)⟩
  have hw : w.asIdeal = CoordinateRing.XYIdeal W x (Polynomial.C y) := rfl
  rw [AlgebraicCurve.Place.eq_ofHeightOneSpectrum_of_XClass_mem_nonunits_of_YClass_mem_nonunits v hX hY w hw,
    WeierstrassCurve.Affine.placeOfPoint_some_eq_ofHeightOneSpectrum h w hw]

end S_WeierstrassCurve_Affine_eq_placeOfPoint_some_of_XClass_mem_nonunits_of_YClass_mem_nonunits
end P2MW
export P2MW.S_WeierstrassCurve_Affine_eq_placeOfPoint_some_of_XClass_mem_nonunits_of_YClass_mem_nonunits (solution)
