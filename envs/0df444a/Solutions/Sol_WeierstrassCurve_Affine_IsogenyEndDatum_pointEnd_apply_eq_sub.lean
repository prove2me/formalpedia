-- Prove2me | solution 1 for WeierstrassCurve.Affine.IsogenyEndDatum.pointEnd_apply_eq_sub
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/412fe9f9-b1d7-5d9d-ba2d-1f0ded8b5588

import Mathlib
import Definitions.Def_Isogeny_ConditionalCurrency
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_Affine_IsogenyEndDatum_pointEnd_apply_eq_sub

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine AlgebraicCurve

universe u

theorem solution
    {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
    {W : WeierstrassCurve.Affine F} [W.IsElliptic] [GenusOnePlaceGate W] [AbelTheorem W]
    (D : IsogenyEndDatum W) (hN : NormFormulaAlong F D.ι D.hfin) (P : W.Point) :
    D.pointEnd hN P
      = (pointEquivPlace (W := W)).symm ((placeOfPoint P).restrictAlong D.ι D.hι)
        - (pointEquivPlace (W := W)).symm ((placeOfPoint (0 : W.Point)).restrictAlong D.ι D.hι) := by

  set Q : W.Point := (pointEquivPlace (W := W)).symm ((placeOfPoint P).restrictAlong D.ι D.hι) with hQ
  set Q₀ : W.Point :=
    (pointEquivPlace (W := W)).symm ((placeOfPoint (0 : W.Point)).restrictAlong D.ι D.hι) with hQ₀
  have hP : (placeOfPoint P).restrictAlong D.ι D.hι = placeOfPoint Q :=
    ((pointEquivPlace (W := W)).apply_symm_apply _).symm
  have h0 : (placeOfPoint (0 : W.Point)).restrictAlong D.ι D.hι = placeOfPoint Q₀ :=
    ((pointEquivPlace (W := W)).apply_symm_apply _).symm

  have hdiv : (Pic0.pushforwardAlongDegZero D.ι D.hι (pointDivisor P) :
      AlgebraicCurve.Divisor F W.FunctionField)
        = Finsupp.single (placeOfPoint Q) 1 - Finsupp.single (placeOfPoint Q₀) 1 := by
    rw [Pic0.coe_pushforwardAlongDegZero, coe_pointDivisor, map_sub,
      pushforwardAlong_single_eq D.ι D.hι, pushforwardAlong_single_eq D.ι D.hι, hP, h0]
  rw [IsogenyEndDatum.pointEnd_apply, pointClass, Pic0.pushforwardAlongHom_mk,
    genusOnePic0Equiv_apply, pic0ToPoint_mk, hdiv, map_sub, divisorSum_single_placeOfPoint,
    divisorSum_single_placeOfPoint, one_smul, one_smul]

end S_WeierstrassCurve_Affine_IsogenyEndDatum_pointEnd_apply_eq_sub
end P2MW
export P2MW.S_WeierstrassCurve_Affine_IsogenyEndDatum_pointEnd_apply_eq_sub (solution)
