-- Prove2me | solution 1 for WeierstrassCurve.Affine.IsogenyHomDatum.pointHom_apply_eq_sub
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/cc15f7dc-ed18-5c54-a0f5-558566a83239

import Mathlib
import Definitions.Def_Isogeny_ConditionalCurrency
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_Affine_IsogenyHomDatum_pointHom_apply_eq_sub

set_option autoImplicit false

noncomputable section

open WeierstrassCurve WeierstrassCurve.Affine AlgebraicCurve

universe u

theorem solution
    {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
    {V₀ V₁ : WeierstrassCurve.Affine F} [V₀.IsElliptic] [GenusOnePlaceGate V₀] [AbelTheorem V₀]
    [V₁.IsElliptic] [GenusOnePlaceGate V₁] [AbelTheorem V₁]
    (φ : IsogenyHomDatum V₀ V₁) (hN : NormFormulaAlong F φ.ι φ.hfin) (P : V₀.Point) :
    φ.pointHom hN P
      = (pointEquivPlace (W := V₁)).symm ((placeOfPoint P).restrictAlong φ.ι φ.hι)
        - (pointEquivPlace (W := V₁)).symm ((placeOfPoint (0 : V₀.Point)).restrictAlong φ.ι φ.hι) := by
  set Q : V₁.Point := (pointEquivPlace (W := V₁)).symm ((placeOfPoint P).restrictAlong φ.ι φ.hι) with hQ
  set Q₀ : V₁.Point :=
    (pointEquivPlace (W := V₁)).symm ((placeOfPoint (0 : V₀.Point)).restrictAlong φ.ι φ.hι) with hQ₀
  have hP : (placeOfPoint P).restrictAlong φ.ι φ.hι = placeOfPoint Q :=
    ((pointEquivPlace (W := V₁)).apply_symm_apply _).symm
  have h0 : (placeOfPoint (0 : V₀.Point)).restrictAlong φ.ι φ.hι = placeOfPoint Q₀ :=
    ((pointEquivPlace (W := V₁)).apply_symm_apply _).symm
  have hdiv : (Pic0.pushforwardAlongDegZero φ.ι φ.hι (pointDivisor P) :
      AlgebraicCurve.Divisor F V₁.FunctionField)
        = Finsupp.single (placeOfPoint Q) 1 - Finsupp.single (placeOfPoint Q₀) 1 := by
    rw [Pic0.coe_pushforwardAlongDegZero, coe_pointDivisor, map_sub,
      pushforwardAlong_single_eq φ.ι φ.hι, pushforwardAlong_single_eq φ.ι φ.hι, hP, h0]
  rw [IsogenyHomDatum.pointHom_apply, pointClass, Pic0.pushforwardAlongHom_mk,
    genusOnePic0Equiv_apply, pic0ToPoint_mk, hdiv, map_sub, divisorSum_single_placeOfPoint,
    divisorSum_single_placeOfPoint, one_smul, one_smul]

end
end S_WeierstrassCurve_Affine_IsogenyHomDatum_pointHom_apply_eq_sub
end P2MW
export P2MW.S_WeierstrassCurve_Affine_IsogenyHomDatum_pointHom_apply_eq_sub (solution)
