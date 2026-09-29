-- Prove2me | solution 1 for WeierstrassCurve.Affine.eq_zero_of_forall_weilPairing0_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/f1d51197-555a-5090-878a-d3e758db2164

import Mathlib
import Definitions.Def_EllipticCurve_WeilPairingFun
import Theorems.Thm_WeierstrassCurve_Affine_eq_zero_of_forall_transEquiv_eq
import Theorems.Thm_WeierstrassCurve_Affine_valuation_mulPull_le_of_ne_zero
import Theorems.Thm_WeierstrassCurve_Affine_valuation_weilFun
import Theorems.Thm_WeierstrassCurve_Affine_exists_transEquiv_weilFun_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_Affine_eq_zero_of_forall_weilPairing0_eq_one
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

open WeierstrassCurve WeierstrassCurve.Affine IsDedekindDomain WithZero

theorem solution {F K : Type*} [Field F] [Field K] [Algebra F K]
    [DecidableEq K] [IsAlgClosed K] (W : WeierstrassCurve F) [W.IsElliptic] [IsDedekindDomain (W⁄K).CoordinateRing]
    {n : ℕ} (hn : (n : K) ≠ 0) (T : (W⁄K).Point) (hT : (n : ℤ) • T = 0)
    (h : ∀ S : (W⁄K).Point, (n : ℤ) • S = 0 → weilPairing0 W K n S T = 1) : T = 0 := by
  refine WeierstrassCurve.Affine.eq_zero_of_forall_transEquiv_eq W hn
    (fun P hP hnP h' k hh => WeierstrassCurve.Affine.valuation_mulPull_le_of_ne_zero W hn P hP hnP h' k hh)
    (weilFun W K n T) ?_ ?_
  · intro P hP hnP
    rw [WeierstrassCurve.Affine.valuation_weilFun W hn hT P hP, if_neg hnP, div_one]
  · intro S hS
    have hc := WeierstrassCurve.Affine.exists_transEquiv_weilFun_eq W hn S T hS hT
    rw [WeierstrassCurve.Affine.transEquiv_weilFun W K hc, h S hS, Units.val_one, map_one, one_mul]

end S_WeierstrassCurve_Affine_eq_zero_of_forall_weilPairing0_eq_one
end P2MW
export P2MW.S_WeierstrassCurve_Affine_eq_zero_of_forall_weilPairing0_eq_one (solution)
