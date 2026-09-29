-- Prove2me | solution 1 for WeierstrassCurve.Affine.weilPairing0_self
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/13424b99-bbdf-5f23-81d2-adcc2660e036

import Mathlib.Data.Set.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Definitions.Def_EllipticCurve_WeilPairingFun
import Theorems.Thm_WeierstrassCurve_Affine_Point_exists_zsmul_eq_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_Affine_FunctionField_exists_eq_algebraMap_of_valuation_eq_one
import Theorems.Thm_WeierstrassCurve_Affine_valuation_transEquiv_weilFun
import Theorems.Thm_WeierstrassCurve_Affine_weilFun_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_Affine_weilPairing0_self
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

theorem transEquiv_weilFun_self {n : ℕ} (hn : (n : K) ≠ 0) {T : (W⁄K).Point}
    (hT : (n : ℤ) • T = 0) : transEquiv W K T (weilFun W K n T) = weilFun W K n T := by
  classical
  haveI : (W⁄K).IsElliptic := by
    dsimp only [Affine.baseChange, WeierstrassCurve.baseChange]; infer_instance
  have hn0 : (n : ℤ) ≠ 0 := by
    have : n ≠ 0 := by rintro rfl; exact hn Nat.cast_zero
    exact_mod_cast this
  obtain ⟨T', hT'⟩ := WeierstrassCurve.Affine.Point.exists_zsmul_eq_of_isAlgClosed (W⁄K) hn0 T
  set g := weilFun W K n T with hg

  set a : ℕ → (W⁄K).FunctionField := fun i => transEquiv W K ((i : ℤ) • T') g with ha
  have hstep : ∀ i, transEquiv W K T' (a i) = a (i + 1) := by
    intro i
    simp only [ha]
    rw [transEquiv_transEquiv, Nat.cast_succ, add_smul, one_smul, add_comm]
  set G := ∏ i ∈ Finset.range n, a i with hG

  have hGval : ∀ (P : (W⁄K).Point) (hP : P ≠ 0),
      (placeOf W K P hP).valuation (W⁄K).FunctionField G = 1 := by
    intro P hP
    rw [hG, map_prod]

    set d : ℤ → ℤᵐ⁰ := fun j => if (n : ℤ) • P + j • T = 0 then exp (-1 : ℤ) else 1 with hd
    have hper : ∀ j, d (j + n) = d j := by
      intro j
      simp only [hd, add_smul, hT, add_zero]
    have hai : ∀ i : ℕ, (placeOf W K P hP).valuation (W⁄K).FunctionField (a i) =
        d ((i : ℤ) - 1) / d i := by
      intro i
      simp only [ha]
      rw [WeierstrassCurve.Affine.valuation_transEquiv_weilFun W hn _ hT P hP]
      have h1 : ((n : ℤ) • (P + (i : ℤ) • T') = T) = ((n : ℤ) • P + ((i : ℤ) - 1) • T = 0) := by
        rw [smul_add, smul_comm, hT', sub_smul, one_smul, ← add_sub_assoc, sub_eq_zero]
      have h2 : ((n : ℤ) • (P + (i : ℤ) • T') = 0) = ((n : ℤ) • P + (i : ℤ) • T = 0) := by
        rw [smul_add, smul_comm, hT']
      simp only [hd, h1, h2]
    simp_rw [hai]
    rw [Finset.prod_div_distrib]
    suffices h : ∏ i ∈ Finset.range n, d ((i : ℤ) - 1) = ∏ i ∈ Finset.range n, d i by
      rw [h, div_self]
      rw [Finset.prod_ne_zero_iff]
      intro i _
      simp only [hd]
      split_ifs
      · exact WithZero.coe_ne_zero
      · exact one_ne_zero
    cases n with
    | zero => simp
    | succ m =>
      rw [Finset.prod_range_succ' (fun i => d ((i : ℤ) - 1)), Finset.prod_range_succ]
      congr 1
      · refine Finset.prod_congr rfl fun i _ => ?_
        push_cast
        ring_nf
      · have := hper (-1)
        push_cast at this ⊢
        rw [← this]
        congr 1
        ring
  obtain ⟨c, hc0, hGc⟩ := exists_eq_algebraMap W hGval

  have hfix : transEquiv W K T' G = G := by rw [hGc, AlgEquiv.commutes]
  have hshift : transEquiv W K T' G = ∏ i ∈ Finset.range n, a (i + 1) := by
    rw [hG, map_prod]
    exact Finset.prod_congr rfl fun i _ => hstep i

  have ha0 : ∀ i, a i ≠ 0 := fun i => by
    simp only [ha]
    exact (map_ne_zero_iff _ (transEquiv W K _).injective).mpr (WeierstrassCurve.Affine.weilFun_ne_zero W hn hT)
  cases hn' : n with
  | zero => exact absurd (by rw [hn', Nat.cast_zero]) hn
  | succ m =>
    rw [hn'] at hshift hG
    rw [hshift, hG, Finset.prod_range_succ, Finset.prod_range_succ' a] at hfix
    have hcancel := mul_left_cancel₀ (Finset.prod_ne_zero_iff.mpr fun i _ => ha0 (i + 1)) hfix

    simp only [ha] at hcancel
    rw [Nat.cast_zero, zero_smul, transEquiv_zero, AlgEquiv.coe_refl, id_eq,
      show (((m + 1 : ℕ) : ℤ)) = (n : ℤ) by rw [hn'], hT'] at hcancel
    exact hcancel

end WeilLaws

theorem solution {F K : Type*} [Field F] [Field K] [Algebra F K] [DecidableEq K] [IsAlgClosed K] (W : WeierstrassCurve F) [W.IsElliptic] [IsDedekindDomain (W⁄K).CoordinateRing] {n : ℕ} (hn : (n : K) ≠ 0) (T : (W⁄K).Point) (hT : (n : ℤ) • T = 0) : weilPairing0 W K n T T = 1 := by
  apply WeilLaws.weilPairing0_eq_of W hn hT
  rw [Units.val_one, map_one, one_mul]
  exact WeilLaws.transEquiv_weilFun_self W hn hT

end S_WeierstrassCurve_Affine_weilPairing0_self
end P2MW
export P2MW.S_WeierstrassCurve_Affine_weilPairing0_self (solution)
