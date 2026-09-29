-- Prove2me | solution 1 for WeierstrassCurve.Affine.weilPairing0_map_algHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/9f47ea7b-1a1f-530b-865f-c583c01e9ec9

import Theorems.Thm_WeierstrassCurve_Affine_exists_ringHom_functionField_baseChange_of_algHom
import Theorems.Thm_WeierstrassCurve_Affine_map_transEquiv_eq_transEquiv_map_of_algHom
import Theorems.Thm_WeierstrassCurve_Affine_exists_map_weilFun_eq_mul_weilFun_map_of_algHom
import Theorems.Thm_WeierstrassCurve_Affine_exists_transEquiv_weilFun_eq
import Theorems.Thm_WeierstrassCurve_Affine_weilFun_ne_zero
import Mathlib
import Definitions.Def_EllipticCurve_WeilPairingFun
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_Affine_weilPairing0_map_algHom
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine IsDedekindDomain WithZero

theorem solution
    {F K K' : Type*} [Field F] [Field K] [Field K'] [Algebra F K] [Algebra F K']
    [DecidableEq K] [DecidableEq K'] [IsAlgClosed K] [IsAlgClosed K']
    (W : WeierstrassCurve F) [W.IsElliptic]
    [IsDedekindDomain (W⁄K).CoordinateRing] [IsDedekindDomain (W⁄K').CoordinateRing]
    (f : K →ₐ[F] K') {n : ℕ} (hn : (n : K) ≠ 0)
    (S T : (W⁄K).Point) (hS : (n : ℤ) • S = 0) (hT : (n : ℤ) • T = 0) :
    ((weilPairing0 W K' n (WeierstrassCurve.Affine.Point.map f S)
        (WeierstrassCurve.Affine.Point.map f T) : K'ˣ) : K') =
      f ((weilPairing0 W K n S T : Kˣ) : K) := by
  classical

  obtain ⟨Φ, hΦ⟩ := WeierstrassCurve.Affine.exists_ringHom_functionField_baseChange_of_algHom (K := K) (K' := K') W f
  have hfinj : Function.Injective f := f.toRingHom.injective
  have hn' : (n : K') ≠ 0 := by
    intro h0; apply hn
    have : f (n : K) = f 0 := by rw [map_natCast, map_zero, h0]
    exact hfinj this

  have hS' : (n : ℤ) • WeierstrassCurve.Affine.Point.map f S = 0 := by
    rw [← map_zsmul (WeierstrassCurve.Affine.Point.map f) (n : ℤ) S, hS, map_zero]
  have hT' : (n : ℤ) • WeierstrassCurve.Affine.Point.map f T = 0 := by
    rw [← map_zsmul (WeierstrassCurve.Affine.Point.map f) (n : ℤ) T, hT, map_zero]

  have hΦc : ∀ c : K, Φ (algebraMap K (W⁄K).FunctionField c) = algebraMap K' (W⁄K').FunctionField (f c) := by
    intro c
    have h1 : algebraMap K (W⁄K).FunctionField c =
        algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField (CoordinateRing.mk (W⁄K) (Polynomial.C (Polynomial.C c))) := by
      rw [IsScalarTower.algebraMap_apply K (W⁄K).CoordinateRing (W⁄K).FunctionField]
      rfl
    have h2 : algebraMap K' (W⁄K').FunctionField (f c) =
        algebraMap (W⁄K').CoordinateRing (W⁄K').FunctionField (CoordinateRing.mk (W⁄K') (Polynomial.C (Polynomial.C (f c)))) := by
      rw [IsScalarTower.algebraMap_apply K' (W⁄K').CoordinateRing (W⁄K').FunctionField]
      rfl
    rw [h1, hΦ, h2]
    simp [Polynomial.map_C]

  set e : K := ((weilPairing0 W K n S T : Kˣ) : K) with he
  set e' : K' := ((weilPairing0 W K' n (WeierstrassCurve.Affine.Point.map f S)
    (WeierstrassCurve.Affine.Point.map f T) : K'ˣ) : K') with he'
  set g' := weilFun W K' n (WeierstrassCurve.Affine.Point.map f T) with hg'def

  have hdefK := transEquiv_weilFun (W := W) (K := K)
    (WeierstrassCurve.Affine.exists_transEquiv_weilFun_eq W hn S T hS hT)
  have hdefK' := transEquiv_weilFun (W := W) (K := K')
    (WeierstrassCurve.Affine.exists_transEquiv_weilFun_eq W hn' _ _ hS' hT')

  obtain ⟨c, hc⟩ := WeierstrassCurve.Affine.exists_map_weilFun_eq_mul_weilFun_map_of_algHom W hn f Φ hΦ hT
  have lhs : Φ (transEquiv W K S (weilFun W K n T)) =
      algebraMap K' (W⁄K').FunctionField (c : K') * (algebraMap K' (W⁄K').FunctionField e' * g') := by
    rw [WeierstrassCurve.Affine.map_transEquiv_eq_transEquiv_map_of_algHom W f Φ hΦ S, hc, map_mul,
      AlgEquiv.commutes, hdefK']
  have rhs : Φ (algebraMap K (W⁄K).FunctionField e * weilFun W K n T) =
      algebraMap K' (W⁄K').FunctionField (f e) * (algebraMap K' (W⁄K').FunctionField (c : K') * g') := by
    rw [map_mul, hΦc, hc]
  have key : algebraMap K' (W⁄K').FunctionField (c : K') * (algebraMap K' (W⁄K').FunctionField e' * g') =
      algebraMap K' (W⁄K').FunctionField (f e) * (algebraMap K' (W⁄K').FunctionField (c : K') * g') := by
    rw [← lhs, ← rhs, hdefK]

  have hg' : g' ≠ 0 := WeierstrassCurve.Affine.weilFun_ne_zero W hn' hT'
  have hc0 : algebraMap K' (W⁄K').FunctionField (c : K') ≠ 0 := by
    rw [map_ne_zero_iff _ (algebraMap K' (W⁄K').FunctionField).injective]; exact c.ne_zero
  have h2 : algebraMap K' (W⁄K').FunctionField (c : K') * g' *
      (algebraMap K' (W⁄K').FunctionField e' - algebraMap K' (W⁄K').FunctionField (f e)) = 0 := by
    have := sub_eq_zero.mpr key
    calc _ = algebraMap K' (W⁄K').FunctionField (c : K') * (algebraMap K' (W⁄K').FunctionField e' * g') -
          algebraMap K' (W⁄K').FunctionField (f e) * (algebraMap K' (W⁄K').FunctionField (c : K') * g') := by ring
      _ = 0 := this
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd h3 (mul_ne_zero hc0 hg')
  · exact (algebraMap K' (W⁄K').FunctionField).injective (sub_eq_zero.mp h3)

end S_WeierstrassCurve_Affine_weilPairing0_map_algHom
end P2MW
export P2MW.S_WeierstrassCurve_Affine_weilPairing0_map_algHom (solution)
