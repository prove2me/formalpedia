-- Prove2me | solution 1 for WeierstrassCurve.Affine.IsogenyHomDatum.pointHom_apply_eq_pointEquivPlace_sub
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/c8e3bea4-e3d8-58c9-bfe8-f9609e38a291

import Mathlib
import Definitions.Def_Isogeny_ConditionalCurrency
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_Affine_IsogenyHomDatum_pointHom_apply_eq_pointEquivPlace_sub

set_option autoImplicit false

noncomputable section

p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_IsogenyHomDatum_pointHom_apply_eq_pointEquivPlace_sub.WeierstrassCurve WeierstrassCurve.Affine P2MW.S_WeierstrassCurve_Affine_IsogenyHomDatum_pointHom_apply_eq_pointEquivPlace_sub.WeierstrassCurve.Affine AlgebraicCurve"

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine IsIntegral"
namespace Affine
p2m_export "WeierstrassCurve.Affine" "FunctionField Point inertiaDegAlong_eq_one pushforwardAlong_single_eq IsogenyHomDatum GenusOnePlaceGate pointEquivPlace placeOfPoint deg_eq_one divisorSum_single_placeOfPoint pointDivisor coe_pointDivisor pointClass AbelTheorem pic0ToPoint_mk genusOnePic0Equiv genusOnePic0Equiv_apply genusOnePic0Equiv_symm_apply"
p2m_open "WeierstrassCurve.Affine WeierstrassCurve"

open AlgebraicCurve

section CharFreeOneLiners

universe v

variable {F : Type v} [Field F] [DecidableEq F]
variable {V W : Affine F}
variable [GenusOnePlaceGate V] [AbelTheorem V] [GenusOnePlaceGate W] [AbelTheorem W]
variable (ι : V.FunctionField →ₐ[F] W.FunctionField) (hι : ι.toRingHom.IsIntegral)

theorem inertiaDegAlong_eq_one_cf (w : AlgebraicCurve.Place F W.FunctionField) :
    w.inertiaDegAlong ι hι = 1 := by
  have h := AlgebraicCurve.Place.deg_restrictAlong_mul_inertiaDegAlong ι hι w
  rw [deg_eq_one (W := V) (w.restrictAlong ι hι), deg_eq_one (W := W) w, one_mul] at h
  exact h

theorem pushforwardAlong_single_eq_cf (w : AlgebraicCurve.Place F W.FunctionField) (n : ℤ) :
    Divisor.pushforwardAlong ι hι (Finsupp.single w n)
      = Finsupp.single (w.restrictAlong ι hι) n := by
  rw [Divisor.pushforwardAlong_single, inertiaDegAlong_eq_one_cf ι hι w, Nat.cast_one, mul_one]

end CharFreeOneLiners

end WeierstrassCurve.Affine

universe u

theorem solution
    {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F]
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
      pushforwardAlong_single_eq_cf φ.ι φ.hι, pushforwardAlong_single_eq_cf φ.ι φ.hι, hP, h0]
  have happ : φ.pointHom hN P
      = genusOnePic0Equiv V₁ (Pic0.pushforwardAlongHom φ.ι φ.hι φ.hfin hN (pointClass P)) := by
    rw [← genusOnePic0Equiv_symm_apply]
    rfl
  rw [happ, pointClass, Pic0.pushforwardAlongHom_mk,
    genusOnePic0Equiv_apply, pic0ToPoint_mk, hdiv, map_sub, divisorSum_single_placeOfPoint,
    divisorSum_single_placeOfPoint, one_smul, one_smul]

end
end S_WeierstrassCurve_Affine_IsogenyHomDatum_pointHom_apply_eq_pointEquivPlace_sub
end P2MW
export P2MW.S_WeierstrassCurve_Affine_IsogenyHomDatum_pointHom_apply_eq_pointEquivPlace_sub (solution)
