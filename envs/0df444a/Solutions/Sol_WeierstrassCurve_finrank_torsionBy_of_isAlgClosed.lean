-- Prove2me | solution 1 for WeierstrassCurve.finrank_torsionBy_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/a80242c6-b434-5b32-8665-bcb29a588618

import Theorems.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_finrank_torsionBy_of_isAlgClosed
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem solution {F : Type*} {K : Type*} [Field F] [Field K] [Algebra F K] [IsAlgClosed K]
    [DecidableEq K] (W : WeierstrassCurve F) [W.IsElliptic] {p : ℕ} [Fact p.Prime]
    (hp : (p : K) ≠ 0) :
    Module.finrank (ZMod p) (Submodule.torsionBy ℤ (W⁄K).Point p) = 2 := by
  have hcard : Nat.card (Submodule.torsionBy ℤ (W⁄K).Point p) = p ^ 2 :=
    WeierstrassCurve.card_torsion_of_isAlgClosed W hp
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  haveI : Finite (Submodule.torsionBy ℤ (W⁄K).Point p) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  haveI : Module.Finite (ZMod p) (Submodule.torsionBy ℤ (W⁄K).Point p) := Module.Finite.of_finite
  have h := Module.natCard_eq_pow_finrank (K := ZMod p) (V := Submodule.torsionBy ℤ (W⁄K).Point p)
  rw [hcard, Nat.card_zmod] at h
  exact (Nat.pow_right_injective hp1 h).symm

end S_WeierstrassCurve_finrank_torsionBy_of_isAlgClosed
end P2MW
export P2MW.S_WeierstrassCurve_finrank_torsionBy_of_isAlgClosed (solution)
