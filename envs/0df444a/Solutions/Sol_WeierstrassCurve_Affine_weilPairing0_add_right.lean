-- Prove2me | solution 1 for WeierstrassCurve.Affine.weilPairing0_add_right
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/9f959fdc-4755-5722-ada7-9dcfef3cdc90

import Mathlib.Data.Set.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Definitions.Def_EllipticCurve_WeilPairingFun
import Theorems.Thm_WeierstrassCurve_Affine_Point_exists_zsmul_eq_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_Affine_FunctionField_exists_eq_algebraMap_of_valuation_eq_one
import Theorems.Thm_WeierstrassCurve_Affine_valuation_transEquiv_weilFun
import Theorems.Thm_WeierstrassCurve_Affine_exists_transEquiv_weilFun_eq
import Theorems.Thm_WeierstrassCurve_Affine_weilFun_ne_zero
import Theorems.Thm_WeierstrassCurve_Affine_valuation_weilFun
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_Affine_weilPairing0_add_right
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

open WeierstrassCurve WeierstrassCurve.Affine IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open scoped nonZeroDivisors

namespace WeilLaws

variable {F : Type*} [Field F] {K : Type*} [Field K] [Algebra F K] [DecidableEq K] [IsAlgClosed K]
  (W : WeierstrassCurve F) [W.IsElliptic]
  [IsDedekindDomain (W⁄K).CoordinateRing]

omit [IsDedekindDomain (W⁄K).CoordinateRing] in
theorem transEquiv_transEquiv (S T : (W⁄K).Point) (h : (W⁄K).FunctionField) :
    transEquiv W K S (transEquiv W K T h) = transEquiv W K (S + T) h := by
  rw [transEquiv_add, AlgEquiv.trans_apply]

omit [IsDedekindDomain (W⁄K).CoordinateRing] in
theorem transEquiv_comm (S T : (W⁄K).Point) (h : (W⁄K).FunctionField) :
    transEquiv W K S (transEquiv W K T h) = transEquiv W K T (transEquiv W K S h) := by
  rw [transEquiv_transEquiv, transEquiv_transEquiv, add_comm]

omit [DecidableEq K] [IsAlgClosed K] [W.IsElliptic] [IsDedekindDomain (W⁄K).CoordinateRing] in

theorem const_unique {g : (W⁄K).FunctionField} (hg : g ≠ 0) {c c' : K}
    (h : algebraMap K (W⁄K).FunctionField c * g = algebraMap K (W⁄K).FunctionField c' * g) :
    c = c' :=
  (algebraMap K (W⁄K).FunctionField).injective (mul_right_cancel₀ hg h)

theorem weilPairing0_eq_of {n : ℕ} (hn : (n : K) ≠ 0) {S T : (W⁄K).Point} (hT : (n : ℤ) • T = 0)
    {c : Kˣ} (h : transEquiv W K S (weilFun W K n T) =
      algebraMap K (W⁄K).FunctionField (c : K) * weilFun W K n T) :
    weilPairing0 W K n S T = c := by
  have h' := transEquiv_weilFun W K ⟨c, h⟩
  rw [h] at h'
  exact (Units.ext (const_unique W (WeierstrassCurve.Affine.weilFun_ne_zero W hn hT) h')).symm

omit [DecidableEq K] in

theorem exists_eq_algebraMap {f : (W⁄K).FunctionField}
    (hf : ∀ (P : (W⁄K).Point) (hP : P ≠ 0), (placeOf W K P hP).valuation (W⁄K).FunctionField f = 1) :
    ∃ c : K, c ≠ 0 ∧ f = algebraMap K (W⁄K).FunctionField c := by
  apply WeierstrassCurve.Affine.FunctionField.exists_eq_algebraMap_of_valuation_eq_one (W := W⁄K)
  intro v
  obtain ⟨P, hP, rfl⟩ := placeOf_surjective W K v
  exact hf P hP

end WeilLaws

theorem solution {F K : Type*} [Field F] [Field K] [Algebra F K] [DecidableEq K] [IsAlgClosed K] (W : WeierstrassCurve F) [W.IsElliptic] [IsDedekindDomain (W⁄K).CoordinateRing] {n : ℕ} (hn : (n : K) ≠ 0) (S T T' : (W⁄K).Point) (hS : (n : ℤ) • S = 0) (hT : (n : ℤ) • T = 0) (hT' : (n : ℤ) • T' = 0) : weilPairing0 W K n S (T + T') = weilPairing0 W K n S T * weilPairing0 W K n S T' := by
  classical
  haveI : (W⁄K).IsElliptic := by
    dsimp only [Affine.baseChange, WeierstrassCurve.baseChange]; infer_instance
  have hn0 : (n : ℤ) ≠ 0 := by
    have : n ≠ 0 := by rintro rfl; exact hn Nat.cast_zero
    exact_mod_cast this
  have hTsum : (n : ℤ) • (T + T') = 0 := by rw [smul_add, hT, hT', add_zero]
  obtain ⟨T₁', hT₁'⟩ := WeierstrassCurve.Affine.Point.exists_zsmul_eq_of_isAlgClosed (W⁄K) hn0 T
  set gT := weilFun W K n T
  set gT2 := weilFun W K n T'
  set gsum := weilFun W K n (T + T')

  set h := gT * transEquiv W K (-T₁') gT2 with hh
  have hh0 : h ≠ 0 := mul_ne_zero (WeierstrassCurve.Affine.weilFun_ne_zero W hn hT)
    ((map_ne_zero_iff _ (transEquiv W K _).injective).mpr (WeierstrassCurve.Affine.weilFun_ne_zero W hn hT'))
  have hg0 : gsum ≠ 0 := WeierstrassCurve.Affine.weilFun_ne_zero W hn hTsum
  have hval : ∀ (P : (W⁄K).Point) (hP : P ≠ 0),
      (placeOf W K P hP).valuation (W⁄K).FunctionField (gsum / h) = 1 := by
    intro P hP
    rw [map_div₀, hh, map_mul, WeierstrassCurve.Affine.valuation_weilFun W hn hTsum P hP,
      WeierstrassCurve.Affine.valuation_weilFun W hn hT P hP, WeierstrassCurve.Affine.valuation_transEquiv_weilFun W hn _ hT' P hP]
    have e1 : ((n : ℤ) • (P + -T₁') = T') = ((n : ℤ) • P = T + T') := by
      rw [smul_add, smul_neg, hT₁', ← sub_eq_add_neg, sub_eq_iff_eq_add, add_comm T' T]
    have e2 : ((n : ℤ) • (P + -T₁') = 0) = ((n : ℤ) • P = T) := by
      rw [smul_add, smul_neg, hT₁', ← sub_eq_add_neg, sub_eq_zero]
    simp only [e1, e2]
    have hne : ∀ c : Prop, ∀ [Decidable c], (if c then (exp (-1 : ℤ) : ℤᵐ⁰) else 1) ≠ 0 := by
      intro c _; split_ifs; exacts [WithZero.coe_ne_zero, one_ne_zero]
    have key : ∀ A B C : ℤᵐ⁰, A ≠ 0 → B ≠ 0 → C ≠ 0 → A / B / (C / B * (A / C)) = 1 := by
      intro A B C hA hB hC
      rw [div_mul_div_comm, mul_comm C A, mul_div_mul_right _ _ hC, div_self (div_ne_zero hA hB)]
    exact key _ _ _ (hne _) (hne _) (hne _)
  obtain ⟨c, hc0, hc⟩ := WeilLaws.exists_eq_algebraMap W hval
  have hgh : gsum = algebraMap K _ c * h := by
    rw [← hc, div_mul_cancel₀ _ hh0]

  obtain ⟨c₁, hc₁⟩ := WeierstrassCurve.Affine.exists_transEquiv_weilFun_eq W hn S T hS hT
  obtain ⟨c₂, hc₂⟩ := WeierstrassCurve.Affine.exists_transEquiv_weilFun_eq W hn S T' hS hT'
  have h1 := WeilLaws.weilPairing0_eq_of W hn hT hc₁
  have h2 := WeilLaws.weilPairing0_eq_of W hn hT' hc₂
  have key : transEquiv W K S gsum = algebraMap K _ ((c₁ * c₂ : Kˣ) : K) * gsum := by
    conv_lhs => rw [hgh, hh]
    rw [map_mul, map_mul, AlgEquiv.commutes, hc₁, WeilLaws.transEquiv_comm, hc₂, map_mul, AlgEquiv.commutes]
    conv_rhs => rw [hgh, hh]
    rw [Units.val_mul, map_mul]
    ring
  rw [WeilLaws.weilPairing0_eq_of W hn hTsum key, h1, h2]

end S_WeierstrassCurve_Affine_weilPairing0_add_right
end P2MW
export P2MW.S_WeierstrassCurve_Affine_weilPairing0_add_right (solution)
