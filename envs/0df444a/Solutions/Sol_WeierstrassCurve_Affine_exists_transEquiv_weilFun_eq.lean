-- Prove2me | solution 1 for WeierstrassCurve.Affine.exists_transEquiv_weilFun_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/1455fb5f-e52c-5d9c-9e81-84decbf6b318

import Definitions.Def_EllipticCurve_WeilPairingFun
import Theorems.Thm_WeierstrassCurve_Affine_valuation_transEquiv_weilFun
import Theorems.Thm_WeierstrassCurve_Affine_valuation_weilFun
import Theorems.Thm_WeierstrassCurve_Affine_weilFun_ne_zero
import Theorems.Thm_WeierstrassCurve_Affine_FunctionField_exists_eq_algebraMap_of_valuation_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_Affine_exists_transEquiv_weilFun_eq
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

open WeierstrassCurve WeierstrassCurve.Affine IsDedekindDomain WithZero

theorem solution {F : Type*} {K : Type*} [Field F] [Field K] [Algebra F K] [DecidableEq K] [IsAlgClosed K] (W : WeierstrassCurve F) [W.IsElliptic] [IsDedekindDomain (W⁄K).CoordinateRing] {n : ℕ} (hn : (n : K) ≠ 0) (S T : (W⁄K).Point) (hS : (n : ℤ) • S = 0) (hT : (n : ℤ) • T = 0) : ∃ c : Kˣ, transEquiv W K S (weilFun W K n T) = algebraMap K (W⁄K).FunctionField (c : K) * weilFun W K n T := by
  have hg0 := weilFun_ne_zero W hn hT
  have hval : ∀ v : HeightOneSpectrum (W⁄K).CoordinateRing,
      v.valuation (W⁄K).FunctionField (transEquiv W K S (weilFun W K n T) / weilFun W K n T) = 1 := by
    intro v
    obtain ⟨P, hP, rfl⟩ := placeOf_surjective W K v
    rw [map_div₀, valuation_transEquiv_weilFun W hn S hT P hP, valuation_weilFun W hn hT P hP, smul_add, hS,
      add_zero, div_self]
    refine div_ne_zero ?_ ?_ <;> split_ifs <;> simp
  obtain ⟨c, hc0, hc⟩ :=
    WeierstrassCurve.Affine.FunctionField.exists_eq_algebraMap_of_valuation_eq_one (W := W.baseChange K) hval
  exact ⟨Units.mk0 c hc0, by rw [Units.val_mk0, ← hc, div_mul_cancel₀ _ hg0]⟩

end S_WeierstrassCurve_Affine_exists_transEquiv_weilFun_eq
end P2MW
export P2MW.S_WeierstrassCurve_Affine_exists_transEquiv_weilFun_eq (solution)
