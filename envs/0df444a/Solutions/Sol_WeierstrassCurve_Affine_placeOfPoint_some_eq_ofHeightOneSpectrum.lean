-- Prove2me | solution 1 for WeierstrassCurve.Affine.placeOfPoint_some_eq_ofHeightOneSpectrum
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/06137338-e725-591a-840c-2b95746b1656

import Mathlib
import Definitions.Def_WeierstrassCurve_GenusOnePlaceGateCentred
import Theorems.Thm_AlgebraicCurve_Place_eq_ofHeightOneSpectrum_of_XClass_mem_nonunits_of_YClass_mem_nonunits
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_Affine_placeOfPoint_some_eq_ofHeightOneSpectrum

set_option autoImplicit false

open AlgebraicCurve WeierstrassCurve WeierstrassCurve.Affine

universe u

theorem solution
    {F : Type u} [Field F] [DecidableEq F] {W : WeierstrassCurve.Affine F}
    [GenusOnePlaceGate W] [GenusOnePlaceGate.IsCentred W] [IsDedekindDomain W.CoordinateRing]
    {x y : F} (h : W.Nonsingular x y)
    (w : IsDedekindDomain.HeightOneSpectrum W.CoordinateRing)
    (hw : w.asIdeal = CoordinateRing.XYIdeal W x (Polynomial.C y)) :
    placeOfPoint (Point.some x y h) = Place.ofHeightOneSpectrum (K := F) w :=
  AlgebraicCurve.Place.eq_ofHeightOneSpectrum_of_XClass_mem_nonunits_of_YClass_mem_nonunits
    (placeOfPoint (Point.some x y h))
    (GenusOnePlaceGate.IsCentred.algebraMap_XClass_mem_nonunits h)
    (GenusOnePlaceGate.IsCentred.algebraMap_YClass_mem_nonunits h) w hw

end S_WeierstrassCurve_Affine_placeOfPoint_some_eq_ofHeightOneSpectrum
end P2MW
export P2MW.S_WeierstrassCurve_Affine_placeOfPoint_some_eq_ofHeightOneSpectrum (solution)
