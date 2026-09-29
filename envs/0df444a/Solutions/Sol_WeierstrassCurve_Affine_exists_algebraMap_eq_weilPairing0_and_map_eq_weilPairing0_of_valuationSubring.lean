-- Prove2me | solution 1 for WeierstrassCurve.Affine.exists_algebraMap_eq_weilPairing0_and_map_eq_weilPairing0_of_valuationSubring
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/d027df61-d4b5-540a-ac90-86f5f8c659dc

import Mathlib
import Definitions.Def_EllipticCurve_WeilPairingFun
import Theorems.Thm_WeierstrassCurve_Affine_Point_zsmul_x_mul_psi_sq
import Theorems.Thm_WeierstrassCurve_Affine_evalEval_psi_sq
import Theorems.Thm_WeierstrassCurve_Affine_Point_smul_some_eq_zero_iff
import Theorems.Thm_WeierstrassCurve_Affine_weilPairing0_add_left
import Theorems.Thm_WeierstrassCurve_Affine_CoordinateRing_isDedekindDomain
import Theorems.Thm_WeierstrassCurve_Affine_valuation_transEquiv_le
import Theorems.Thm_WeierstrassCurve_Affine_valuation_weilNum
import Theorems.Thm_WeierstrassCurve_Affine_weilNum_ne_zero
import Theorems.Thm_WeierstrassCurve_Affine_exists_transEquiv_weilFun_eq
import Theorems.Thm_WeierstrassCurve_Affine_exists_smul_basis_eq_algebraMap_mul_weilNum_of_valuationSubring
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_Affine_exists_algebraMap_eq_weilPairing0_and_map_eq_weilPairing0_of_valuationSubring
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

universe u

open Polynomial
open scoped Polynomial.Bivariate
p2m_open "WeierstrassCurve~evalEval_φ WeierstrassCurve.Affine IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero"

namespace P2M
namespace WeilVal

p2m_open "WeierstrassCurve~evalEval_φ"

section Eval

variable {F K : Type*} [Field F] [Field K] [Algebra F K] (W : WeierstrassCurve F)

scoped instance isElliptic_baseChange [W.IsElliptic] : (W.baseChange K).IsElliptic :=
  show (W.map (algebraMap F K)).IsElliptic from inferInstance

private scoped instance _root_.P2M.WeilVal.isDedekindDomain [IsAlgClosed K] [W.IsElliptic] : IsDedekindDomain (W⁄K).CoordinateRing :=
  WeierstrassCurve.Affine.CoordinateRing.isDedekindDomain (W.baseChange K)

p2m_export "P2M.WeilVal" "isDedekindDomain"

theorem evalAt_smul_basis {a b : K} (h : (W⁄K).Equation a b) (p q : K[X]) :
    CoordinateRing.evalAt W K h (p • (1 : (W⁄K).CoordinateRing) + q • CoordinateRing.mk (W⁄K) Y) =
      p.eval a + q.eval a * b := by
  rw [map_add, CoordinateRing.smul, CoordinateRing.smul, mul_one, map_mul, CoordinateRing.evalAt_mk,
    CoordinateRing.evalAt_mk, CoordinateRing.evalAt_mk, evalEval_C, evalEval_C, evalEval_X]

theorem evalAt_algebraMap {a b : K} (h : (W⁄K).Equation a b) (c : K) :
    CoordinateRing.evalAt W K h (algebraMap K (W⁄K).CoordinateRing c) = c := by
  change CoordinateRing.evalAt W K h (CoordinateRing.mk (W⁄K) (C (C c))) = c
  rw [CoordinateRing.evalAt_mk, evalEval_C, eval_C]

variable [IsAlgClosed K] [W.IsElliptic]

theorem cong_evalAt (P : (W⁄K).Point) (hP : P ≠ 0) (b : (W⁄K).CoordinateRing) :
    ((placeOf W K P hP).valuation (W⁄K).FunctionField).Cong
      (algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField b)
      (algebraMap K (W⁄K).FunctionField (CoordinateRing.evalAt W K (Point.nonsingular_xc_yc hP).left b)) := by
  rw [Valuation.cong_iff, IsScalarTower.algebraMap_apply K (W⁄K).CoordinateRing (W⁄K).FunctionField,
    ← map_sub]
  apply (valuation_lt_one_iff_mem _ _).mpr
  rw [mem_placeOf_iff W K P hP, map_sub, evalAt_algebraMap, sub_self]

theorem evalAt_eq_zero_iff (P : (W⁄K).Point) (hP : P ≠ 0) (b : (W⁄K).CoordinateRing) :
    CoordinateRing.evalAt W K (Point.nonsingular_xc_yc hP).left b = 0 ↔
      (placeOf W K P hP).valuation (W⁄K).FunctionField
        (algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField b) < 1 := by
  rw [valuation_lt_one_iff_mem, mem_placeOf_iff W K P hP]

variable [DecidableEq K]

theorem evalAt_weilNum_eq_zero_iff {n : ℕ} (hn : (n : K) ≠ 0) {T : (W⁄K).Point} (hT : (n : ℤ) • T = 0)
    (P : (W⁄K).Point) (hP : P ≠ 0) :
    CoordinateRing.evalAt W K (Point.nonsingular_xc_yc hP).left (weilNum W K n T) = 0 ↔ (n : ℤ) • P = T := by
  rw [evalAt_eq_zero_iff W P hP, valuation_weilNum W hn hT P hP]
  by_cases h : (n : ℤ) • P = T
  · simp only [h, if_true, iff_true]
    rw [← exp_zero, exp_lt_exp]; norm_num
  · simp only [h, if_false, lt_self_iff_false]

omit [DecidableEq K] in

theorem eq_of_cong_algebraMap (P : (W⁄K).Point) (hP : P ≠ 0) {c d : K}
    (h : ((placeOf W K P hP).valuation (W⁄K).FunctionField).Cong (algebraMap K _ c) (algebraMap K _ d)) :
    c = d := by
  by_contra hcd
  rw [Valuation.cong_iff, ← map_sub, valuation_algebraMap_eq_one W K P hP (sub_ne_zero.mpr hcd)] at h
  exact lt_irrefl _ h

omit [IsAlgClosed K] [W.IsElliptic] [DecidableEq K] in

theorem evalAt_congr_point {P : (W⁄K).Point} (hP : P ≠ 0) {a b : K} {h' : (W⁄K).Nonsingular a b}
    (hPQ : P = Point.some a b h') (g : (W⁄K).CoordinateRing) :
    CoordinateRing.evalAt W K (Point.nonsingular_xc_yc hP).left g = CoordinateRing.evalAt W K h'.left g := by
  subst hPQ
  rfl

theorem eval_formula {n : ℕ} (hn : (n : K) ≠ 0) {T : (W⁄K).Point} (hT : (n : ℤ) • T = 0)
    {xS yS : K} (hS : (W⁄K).Nonsingular xS yS) (hSn : (n : ℤ) • Point.some xS yS hS = 0)
    {x y : K} (hX : (W⁄K).Nonsingular x y) (hx : x ≠ xS)
    (hX₁ : (n : ℤ) • Point.some x y hX ≠ T) (hX₂ : (n : ℤ) • Point.some x y hX ≠ 0) :
    ∃ (x' y' : K) (hX' : (W⁄K).Nonsingular x' y'),
      Point.some x y hX + Point.some xS yS hS = Point.some x' y' hX' ∧
      CoordinateRing.evalAt W K hX.left (weilNum W K n T) ≠ 0 ∧
      CoordinateRing.evalAt W K hX'.left (weilNum W K n 0) ≠ 0 ∧
      ((weilPairing0 W K n (Point.some xS yS hS) T : Kˣ) : K) *
          CoordinateRing.evalAt W K hX.left (weilNum W K n T) *
          CoordinateRing.evalAt W K hX'.left (weilNum W K n 0) =
        CoordinateRing.evalAt W K hX'.left (weilNum W K n T) *
          CoordinateRing.evalAt W K hX.left (weilNum W K n 0) := by
  have hXS' := (W⁄K).nonsingular_add hX hS fun h => hx h.1
  have hXZ : Point.some x y hX + Point.some xS yS hS = Point.some _ _ hXS' := Point.add_of_X_ne hx
  refine ⟨_, _, hXS', hXZ, ?_⟩
  have hX0 : Point.some x y hX ≠ 0 := Point.some_ne_zero _
  have hS0 : Point.some xS yS hS ≠ 0 := Point.some_ne_zero _
  have hZ0 : Point.some _ _ hXS' ≠ 0 := Point.some_ne_zero _
  have hXS0 : Point.some x y hX + Point.some xS yS hS ≠ 0 := by rw [hXZ]; exact hZ0
  have h0T : (n : ℤ) • (0 : (W⁄K).Point) = 0 := smul_zero _

  have hZ₁ : (n : ℤ) • Point.some _ _ hXS' ≠ T := by
    rw [← hXZ, smul_add, hSn, add_zero]; exact hX₁
  have hZ₂ : (n : ℤ) • Point.some _ _ hXS' ≠ 0 := by
    rw [← hXZ, smul_add, hSn, add_zero]; exact hX₂
  have eXT : CoordinateRing.evalAt W K hX.left (weilNum W K n T) ≠ 0 :=
    fun h => hX₁ ((evalAt_weilNum_eq_zero_iff W hn hT _ hX0).mp h)
  have eZO : CoordinateRing.evalAt W K hXS'.left (weilNum W K n 0) ≠ 0 :=
    fun h => hZ₂ ((evalAt_weilNum_eq_zero_iff W hn h0T _ hZ0).mp h)
  refine ⟨eXT, eZO, ?_⟩

  have hdef := transEquiv_weilFun W K (exists_transEquiv_weilFun_eq W hn (Point.some xS yS hS) T hSn hT)
  have hNO0 : algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField (weilNum W K n 0) ≠ 0 :=
    fun h => weilNum_ne_zero W hn h0T ((map_eq_zero_iff _ (IsFractionRing.injective _ _)).mp h)
  have hτNO0 : transEquiv W K (Point.some xS yS hS) (algebraMap _ (W⁄K).FunctionField (weilNum W K n 0)) ≠ 0 :=
    fun h => hNO0 ((map_eq_zero_iff _ (transEquiv W K (Point.some xS yS hS)).injective).mp h)

  have hid : transEquiv W K (Point.some xS yS hS) (algebraMap _ (W⁄K).FunctionField (weilNum W K n T)) *
        algebraMap _ (W⁄K).FunctionField (weilNum W K n 0) =
      algebraMap K (W⁄K).FunctionField ((weilPairing0 W K n (Point.some xS yS hS) T : Kˣ) : K) *
        algebraMap _ (W⁄K).FunctionField (weilNum W K n T) *
        transEquiv W K (Point.some xS yS hS) (algebraMap _ (W⁄K).FunctionField (weilNum W K n 0)) := by
    rw [weilFun, map_div₀, div_eq_iff hτNO0] at hdef
    rw [hdef]
    field_simp

  have cNT := cong_evalAt W (Point.some x y hX) hX0 (weilNum W K n T)
  have cNO := cong_evalAt W (Point.some x y hX) hX0 (weilNum W K n 0)

  have hxc : (Point.some x y hX).xc ≠ (Point.some xS yS hS).xc := hx
  have cτ : ∀ b : (W⁄K).CoordinateRing,
      ((placeOf W K _ hX0).valuation (W⁄K).FunctionField).Cong
        (transEquiv W K (Point.some xS yS hS) (algebraMap _ (W⁄K).FunctionField b))
        (algebraMap K (W⁄K).FunctionField (CoordinateRing.evalAt W K hXS'.left b)) := by
    intro b
    have hZS : ((placeOf W K _ hXS0).valuation (W⁄K).FunctionField)
        (algebraMap _ (W⁄K).FunctionField b -
          algebraMap K (W⁄K).FunctionField (CoordinateRing.evalAt W K hXS'.left b)) ≤ exp (-((1 : ℕ) : ℤ)) := by
      rw [Nat.cast_one, ← lt_one_iff_le_exp_neg_one]
      have := cong_evalAt W _ hXS0 b
      rwa [evalAt_congr_point W hXS0 hXZ] at this
    have ht := valuation_transEquiv_le W K hX0 hS0 hxc hXS0 _ 1 hZS
    rw [Nat.cast_one, ← lt_one_iff_le_exp_neg_one, map_sub, AlgEquiv.commutes] at ht
    exact ht
  have cτNT := cτ (weilNum W K n T)
  have cτNO := cτ (weilNum W K n 0)
  have h1 : ∀ c : K, (placeOf W K _ hX0).valuation (W⁄K).FunctionField (algebraMap K (W⁄K).FunctionField c) ≤ 1 :=
    valuation_algebraMap_le_one W K _ hX0

  have lhs := cτNT.mul cNO (h1 _) (h1 _)
  have rhs := ((Valuation.Cong.refl (algebraMap K (W⁄K).FunctionField
    ((weilPairing0 W K n (Point.some xS yS hS) T : Kˣ) : K))).mul cNT (h1 _) (h1 _)).mul cτNO
      (by rw [← map_mul]; exact h1 _) (h1 _)
  rw [← map_mul] at lhs
  rw [← map_mul, ← map_mul, ← hid] at rhs
  exact eq_of_cong_algebraMap W _ hX0 (rhs.symm.trans lhs)

end Eval

section Tools

theorem evalEval_eq_of_mk_eq {R : Type*} [CommRing R] (W : WeierstrassCurve R) {x y : R} (h : W.toAffine.Equation x y)
    {p q : R[X][Y]} (hpq : Affine.CoordinateRing.mk W.toAffine p = Affine.CoordinateRing.mk W.toAffine q) :
    p.evalEval x y = q.evalEval x y := by
  obtain ⟨r, hr⟩ := AdjoinRoot.mk_eq_mk.mp hpq
  have h0 : W.toAffine.polynomial.evalEval x y = 0 := h
  have : (p - q).evalEval x y = 0 := by
    rw [hr, Polynomial.evalEval, Polynomial.eval_mul, Polynomial.eval_mul]
    change W.toAffine.polynomial.evalEval x y * r.evalEval x y = 0
    rw [h0, zero_mul]
  rwa [Polynomial.evalEval, Polynomial.eval_sub, Polynomial.eval_sub, sub_eq_zero] at this

theorem evalEval_φ {R : Type*} [CommRing R] (W : WeierstrassCurve R) {x y : R} (h : W.toAffine.Equation x y) (n : ℤ) :
    (W.φ n).evalEval x y = (W.Φ n).eval x := by
  rw [evalEval_eq_of_mk_eq W h (Affine.CoordinateRing.mk_φ W n), Polynomial.evalEval_C]

theorem monic_Phi_sub {R : Type*} [CommRing R] [Nontrivial R] (W : WeierstrassCurve R) {n : ℤ} (hn : n ≠ 0) (c : R) :
    (W.Φ n - Polynomial.C c * W.ΨSq n).Monic := by
  have hlt : (Polynomial.C c * W.ΨSq n).natDegree < (W.Φ n).natDegree := by
    rw [WeierstrassCurve.natDegree_Φ]
    refine lt_of_le_of_lt (Polynomial.natDegree_C_mul_le _ _) (lt_of_le_of_lt (WeierstrassCurve.natDegree_ΨSq_le W n) ?_)
    have : 0 < n.natAbs ^ 2 := pow_pos (Int.natAbs_pos.mpr hn) 2
    omega
  rw [Polynomial.Monic, Polynomial.leadingCoeff_sub_of_degree_lt (Polynomial.degree_lt_degree hlt),
    WeierstrassCurve.leadingCoeff_Φ]

theorem mem_of_root_monic {K : Type*} [Field K] (𝒪 : ValuationSubring K) {p : Polynomial 𝒪} (hp : p.Monic) {a : K}
    (ha : (p.map (algebraMap 𝒪 K)).eval a = 0) : a ∈ 𝒪 := by
  have hint : IsIntegral 𝒪 a := ⟨p, hp, by rwa [Polynomial.eval_map] at ha⟩
  obtain ⟨b, hb⟩ := (IsIntegrallyClosed.isIntegral_iff (R := 𝒪) (K := K)).mp hint
  rw [← hb]
  exact b.2

theorem yc_mem_of_xc_mem {K : Type*} [Field K] (𝒪 : ValuationSubring K) (W : WeierstrassCurve 𝒪) {xR yR : K}
    (heq : (W.map (algebraMap 𝒪 K)).toAffine.Equation xR yR) (hx : xR ∈ 𝒪) : yR ∈ 𝒪 := by
  obtain ⟨x₀, rfl⟩ : ∃ x₀ : 𝒪, algebraMap 𝒪 K x₀ = xR := ⟨⟨xR, hx⟩, rfl⟩
  let r : Polynomial 𝒪 := Polynomial.C (W.a₁ * x₀ + W.a₃) * Polynomial.X -
    Polynomial.C (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)
  have hr : r.degree < (2 : ℕ) := by
    refine lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt ?_ ?_)
    · exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_le _) (by exact_mod_cast Nat.one_lt_two)
    · exact lt_of_le_of_lt Polynomial.degree_C_le (by exact_mod_cast Nat.zero_lt_two)
  have hq : (Polynomial.X ^ 2 + r).Monic := Polynomial.monic_X_pow_add hr
  refine mem_of_root_monic 𝒪 hq ?_
  have he : (W.map (algebraMap 𝒪 K)).toAffine.polynomial.evalEval (algebraMap 𝒪 K x₀) yR = 0 := heq
  rw [WeierstrassCurve.Affine.evalEval_polynomial, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at he
  have hev : ((Polynomial.X ^ 2 + r).map (algebraMap 𝒪 K)).eval yR =
      yR ^ 2 + (algebraMap 𝒪 K W.a₁ * algebraMap 𝒪 K x₀ + algebraMap 𝒪 K W.a₃) * yR -
        (algebraMap 𝒪 K x₀ ^ 3 + algebraMap 𝒪 K W.a₂ * algebraMap 𝒪 K x₀ ^ 2 + algebraMap 𝒪 K W.a₄ * algebraMap 𝒪 K x₀ +
          algebraMap 𝒪 K W.a₆) := by
    simp only [r, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sub, Polynomial.map_mul,
      Polynomial.map_C, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_C, map_add, map_mul, map_pow]
    ring
  rw [hev]
  linear_combination he

scoped instance isElliptic_baseChange' {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (W : WeierstrassCurve R)
    [W.IsElliptic] : (W.baseChange A).IsElliptic :=
  show (W.map (algebraMap R A)).IsElliptic from inferInstance

theorem weilPairing0_pow_eq_one {F K : Type*} [Field F] [Field K] [Algebra F K] [DecidableEq K] [IsAlgClosed K]
    (W : WeierstrassCurve F) [W.IsElliptic] {n : ℕ} (hn : (n : K) ≠ 0) (S T : (W.baseChange K).toAffine.Point)
    (hS : (n : ℤ) • S = 0) (hT : (n : ℤ) • T = 0) :
    WeierstrassCurve.Affine.weilPairing0 W K n S T ^ n = 1 := by
  haveI := WeierstrassCurve.Affine.CoordinateRing.isDedekindDomain (W.baseChange K)
  have h0 : WeierstrassCurve.Affine.weilPairing0 W K n 0 T = 1 := by
    have := WeierstrassCurve.Affine.weilPairing0_add_left W hn 0 0 T (smul_zero _) (smul_zero _) hT
    rw [add_zero] at this
    exact mul_eq_right.mp this.symm
  have hk : ∀ k : ℕ, WeierstrassCurve.Affine.weilPairing0 W K n ((k : ℤ) • S) T =
      WeierstrassCurve.Affine.weilPairing0 W K n S T ^ k := by
    intro k
    induction k with
    | zero => rw [Nat.cast_zero, zero_smul, pow_zero, h0]
    | succ k ih =>
      have hkS : (n : ℤ) • ((k : ℤ) • S) = 0 := by rw [smul_smul, mul_comm, ← smul_smul, hS, smul_zero]
      rw [Nat.cast_succ, add_smul, one_smul, WeierstrassCurve.Affine.weilPairing0_add_left W hn _ _ T hkS hS hT, ih, pow_succ]
  rw [← hk n, hS, h0]

theorem exists_algebraMap_eq_weilPairing0 {K : Type*} [Field K] [DecidableEq K] [IsAlgClosed K] (𝒪 : ValuationSubring K)
    (WK : WeierstrassCurve K) [WK.IsElliptic] {n : ℕ} (hn : (n : K) ≠ 0) (S T : (WK.baseChange K).toAffine.Point)
    (hS : (n : ℤ) • S = 0) (hT : (n : ℤ) • T = 0) :
    ∃ u : 𝒪, algebraMap 𝒪 K u = ((WeierstrassCurve.Affine.weilPairing0 WK K n S T : Kˣ) : K) := by
  have hpow := weilPairing0_pow_eq_one WK hn S T hS hT
  have hn0 : n ≠ 0 := by rintro rfl; exact hn (by simp)
  set e : K := ((WeierstrassCurve.Affine.weilPairing0 WK K n S T : Kˣ) : K)
  have he : e ^ n = 1 := by
    change ((WeierstrassCurve.Affine.weilPairing0 WK K n S T : Kˣ) : K) ^ n = 1
    rw [← Units.val_pow_eq_pow_val, hpow, Units.val_one]
  have hmonic : (Polynomial.X ^ n - 1 : Polynomial 𝒪).Monic := by
    simpa only [map_one] using Polynomial.monic_X_pow_sub_C (1 : 𝒪) hn0
  have hmem : e ∈ 𝒪 := mem_of_root_monic 𝒪 hmonic (by
    rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one, Polynomial.eval_sub,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one, he, sub_self])
  exact ⟨⟨e, hmem⟩, rfl⟩

section Surj

variable {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K] (𝒪 : ValuationSubring K)

omit [DecidableEq K] in

theorem exists_multiset_prod_eq (F : Polynomial 𝒪) (hF : F.Monic) :
    ∃ t : Multiset 𝒪, F = (t.map fun ξ => Polynomial.X - Polynomial.C ξ).prod := by
  induction hd : F.natDegree using Nat.strong_induction_on generalizing F with
  | _ d ih =>
    rcases Nat.eq_zero_or_pos d with rfl | hdpos
    · refine ⟨0, ?_⟩
      rw [Multiset.map_zero, Multiset.prod_zero]
      exact Polynomial.eq_one_of_monic_natDegree_zero hF hd
    ·
      have hdeg : (F.map (algebraMap 𝒪 K)).degree ≠ 0 := by
        rw [hF.degree_map, Polynomial.degree_eq_natDegree hF.ne_zero, hd]
        exact_mod_cast hdpos.ne'
      obtain ⟨ξ, hξ⟩ := IsAlgClosed.exists_root (F.map (algebraMap 𝒪 K)) hdeg
      have hξmem : ξ ∈ 𝒪 := mem_of_root_monic 𝒪 hF hξ
      obtain ⟨ξ₀, rfl⟩ : ∃ ξ₀ : 𝒪, algebraMap 𝒪 K ξ₀ = ξ := ⟨⟨ξ, hξmem⟩, rfl⟩
      have hroot : F.IsRoot ξ₀ := by
        have h1 : algebraMap 𝒪 K (F.eval ξ₀) = 0 := by
          rw [← Polynomial.eval₂_at_apply, ← Polynomial.eval_map]; exact hξ
        exact (map_eq_zero_iff _ (IsFractionRing.injective 𝒪 K)).mp h1
      have hfac : (Polynomial.X - Polynomial.C ξ₀) * (F /ₘ (Polynomial.X - Polynomial.C ξ₀)) = F :=
        Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hroot
      have hG : (F /ₘ (Polynomial.X - Polynomial.C ξ₀)).Monic :=
        Polynomial.Monic.of_mul_monic_left (Polynomial.monic_X_sub_C ξ₀) (hfac.symm ▸ hF)
      have hGdeg : (F /ₘ (Polynomial.X - Polynomial.C ξ₀)).natDegree = d - 1 := by
        have := congrArg Polynomial.natDegree hfac
        rw [(Polynomial.monic_X_sub_C ξ₀).natDegree_mul hG, Polynomial.natDegree_X_sub_C, hd] at this
        omega
      obtain ⟨t, ht⟩ := ih (d - 1) (by omega) _ hG hGdeg
      refine ⟨ξ₀ ::ₘ t, ?_⟩
      rw [Multiset.map_cons, Multiset.prod_cons, ← ht, hfac]

omit [DecidableEq K] in

theorem exists_root_of_eval_map_eq_zero {Ω : Type*} [Field Ω] (ψ : 𝒪 →+* Ω) (F : Polynomial 𝒪) (hF : F.Monic) {a : Ω}
    (ha : (F.map ψ).eval a = 0) : ∃ ξ : 𝒪, F.eval ξ = 0 ∧ ψ ξ = a := by
  obtain ⟨t, rfl⟩ := exists_multiset_prod_eq 𝒪 F hF
  rw [Polynomial.map_multiset_prod, Multiset.map_map, Polynomial.eval_multiset_prod, Multiset.map_map,
    Multiset.prod_eq_zero_iff, Multiset.mem_map] at ha
  obtain ⟨ξ, hξt, hξ⟩ := ha
  simp only [Function.comp_apply, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at hξ
  refine ⟨ξ, ?_, hξ.symm⟩
  rw [Polynomial.eval_multiset_prod, Multiset.map_map, Multiset.prod_eq_zero_iff, Multiset.mem_map]
  exact ⟨ξ, hξt, by simp⟩

theorem exists_nonsingular {F : Type*} [Field F] [IsAlgClosed F] (W : WeierstrassCurve F) [W.IsElliptic] (x : F) :
    ∃ y : F, W.toAffine.Nonsingular x y := by
  let q : Polynomial F := Polynomial.X ^ 2 + (Polynomial.C (W.a₁ * x + W.a₃) * Polynomial.X -
    Polynomial.C (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆))
  have hq : q.degree ≠ 0 := by
    have hr : (Polynomial.C (W.a₁ * x + W.a₃) * Polynomial.X -
        Polynomial.C (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)).degree < ((2 : ℕ) : WithBot ℕ) := by
      refine lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt ?_ ?_)
      · exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_le _) (by exact_mod_cast Nat.one_lt_two)
      · exact lt_of_le_of_lt Polynomial.degree_C_le (by exact_mod_cast Nat.zero_lt_two)
    have h2 : q.degree = ((2 : ℕ) : WithBot ℕ) := by
      have hX : (Polynomial.X ^ 2 : Polynomial F).degree = ((2 : ℕ) : WithBot ℕ) := Polynomial.degree_X_pow 2
      rw [← hX] at hr
      rw [← hX]
      exact Polynomial.degree_add_eq_left_of_degree_lt hr
    rw [h2]; exact ne_of_beq_false rfl
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root q hq
  refine ⟨y, WeierstrassCurve.Affine.equation_iff_nonsingular.mp ?_⟩
  rw [WeierstrassCurve.Affine.Equation, WeierstrassCurve.Affine.evalEval_polynomial]
  simp only [q, Polynomial.IsRoot.def, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_C] at hy
  linear_combination hy

end Surj

end Tools

section Residue

variable {K : Type*} [Field K] [IsAlgClosed K] (𝒪 : ValuationSubring K)

theorem infinite_residueField : Infinite (IsLocalRing.ResidueField 𝒪) := by
  by_contra hfin
  rw [not_infinite_iff_finite] at hfin
  haveI : Fintype (IsLocalRing.ResidueField 𝒪) := Fintype.ofFinite _
  set q := Fintype.card (IsLocalRing.ResidueField 𝒪) with hq
  have hq1 : 1 < q := Fintype.one_lt_card

  set G : Polynomial 𝒪 := X ^ q + (-X + 1) with hG
  have hlt : (-X + 1 : Polynomial 𝒪).degree < ((X : Polynomial 𝒪) ^ q).degree := by
    rw [degree_X_pow]
    refine (degree_add_le _ _).trans_lt (max_lt ?_ ?_)
    · rw [degree_neg, degree_X]; exact_mod_cast hq1
    · exact (degree_one_le).trans_lt (by exact_mod_cast (zero_lt_one.trans hq1))
  have hGm : G.Monic := (monic_X_pow q).add_of_left hlt
  have hGdeg : G.degree = q := by
    rw [hG, degree_add_eq_left_of_degree_lt hlt, degree_X_pow]
  have hdeg0 : (G.map (algebraMap 𝒪 K)).degree ≠ 0 := by
    rw [hGm.degree_map, hGdeg]
    exact_mod_cast (zero_lt_one.trans hq1).ne'
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_root _ hdeg0
  have hαmem : α ∈ 𝒪 := mem_of_root_monic 𝒪 hGm hα
  obtain ⟨a, rfl⟩ : ∃ a : 𝒪, algebraMap 𝒪 K a = α := ⟨⟨α, hαmem⟩, rfl⟩
  have hGa : G.eval a = 0 := by
    have h1 : algebraMap 𝒪 K (G.eval a) = 0 := by
      rw [← Polynomial.eval₂_at_apply, ← Polynomial.eval_map]; exact hα
    exact (map_eq_zero_iff _ (IsFractionRing.injective 𝒪 K)).mp h1
  have hres := congrArg (IsLocalRing.residue 𝒪) hGa
  rw [map_zero, ← Polynomial.eval₂_at_apply, hG] at hres
  simp only [eval₂_add, eval₂_X_pow, eval₂_neg, eval₂_X, eval₂_one] at hres
  rw [hq, FiniteField.pow_card, add_neg_cancel_left] at hres
  exact one_ne_zero hres

theorem exists_residue_notMem (B : Finset (IsLocalRing.ResidueField 𝒪)) :
    ∃ ξ : 𝒪, IsLocalRing.residue 𝒪 ξ ∉ B := by
  haveI := infinite_residueField 𝒪
  obtain ⟨r, hr⟩ := Infinite.exists_notMem_finset B
  obtain ⟨ξ, rfl⟩ := IsLocalRing.residue_surjective r
  exact ⟨ξ, hr⟩

omit [IsAlgClosed K] in

theorem isUnit_sub_of_residue_ne {ξ ζ : 𝒪} (h : IsLocalRing.residue 𝒪 ξ ≠ IsLocalRing.residue 𝒪 ζ) :
    IsUnit (ξ - ζ) := by
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_sub, sub_ne_zero]
  exact h

omit [IsAlgClosed K] in

theorem map_ne_of_residue_ne {Ω : Type*} [Field Ω] (ψ : 𝒪 →+* Ω) {ξ ζ : 𝒪}
    (h : IsLocalRing.residue 𝒪 ξ ≠ IsLocalRing.residue 𝒪 ζ) : ψ ξ ≠ ψ ζ := by
  intro he
  have h0 : ψ (ξ - ζ) = 0 := by rw [map_sub, he, sub_self]
  exact ((isUnit_sub_of_residue_ne 𝒪 h).map ψ).ne_zero h0

omit [IsAlgClosed K] in

theorem mem_of_eval_prod_eq_zero {t : Multiset 𝒪} {ζ : 𝒪}
    (h : ((t.map fun ξ => X - C ξ).prod).eval ζ = 0) : ζ ∈ t := by
  rw [eval_multiset_prod, Multiset.map_map, Multiset.prod_eq_zero_iff, Multiset.mem_map] at h
  obtain ⟨ξ, hξ, h0⟩ := h
  simp only [Function.comp_apply, eval_sub, eval_X, eval_C, sub_eq_zero] at h0
  exact h0 ▸ hξ

end Residue

section Chord

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) {A : Type*} [Field A] [DecidableEq A] (f : R →+* A)

theorem exists_some_add_some_eq {V : WeierstrassCurve A} (hV : V = W.map f)
    {ξ η xS yS e' : R} (he : (ξ - xS) * e' = 1) (hx : f ξ ≠ f xS)
    (hX : V.toAffine.Nonsingular (f ξ) (f η)) (hS : V.toAffine.Nonsingular (f xS) (f yS)) :
    ∃ hZ : V.toAffine.Nonsingular (f (W.toAffine.addX ξ xS ((η - yS) * e')))
        (f (W.toAffine.addY ξ xS η ((η - yS) * e'))),
      WeierstrassCurve.Affine.Point.some _ _ hX + WeierstrassCurve.Affine.Point.some _ _ hS =
        WeierstrassCurve.Affine.Point.some _ _ hZ := by
  subst hV
  have hslope : (W.map f).toAffine.slope (f ξ) (f xS) (f η) (f yS) = f ((η - yS) * e') := by
    rw [WeierstrassCurve.Affine.slope_of_X_ne hx, div_eq_iff (sub_ne_zero.mpr hx), ← map_sub, ← map_sub, ← map_mul,
      mul_assoc, mul_comm e', he, mul_one]
  have hns := (W.map f).toAffine.nonsingular_add hX hS (fun h => hx h.1)
  rw [hslope, WeierstrassCurve.Affine.map_addX, WeierstrassCurve.Affine.map_addY] at hns
  refine ⟨hns, ?_⟩
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne hx]

  have hxZ : (W.map f).toAffine.addX (f ξ) (f xS) ((W.map f).toAffine.slope (f ξ) (f xS) (f η) (f yS)) =
      f (W.toAffine.addX ξ xS ((η - yS) * e')) := by
    rw [hslope, WeierstrassCurve.Affine.map_addX]
  have hyZ : (W.map f).toAffine.addY (f ξ) (f xS) (f η) ((W.map f).toAffine.slope (f ξ) (f xS) (f η) (f yS)) =
      f (W.toAffine.addY ξ xS η ((η - yS) * e')) := by
    rw [hslope, WeierstrassCurve.Affine.map_addY]
  simp only [hxZ, hyZ]

end Chord

section Main

scoped instance isElliptic_baseChange_map {K : Type*} [Field K] (𝒪 : ValuationSubring K) (W : WeierstrassCurve 𝒪)
    [W.IsElliptic] {A : Type*} [CommRing A] (f : 𝒪 →+* A) (B : Type*) [CommRing B] [Algebra A B] :
    ((W.map f).baseChange B).IsElliptic :=
  show ((W.map f).map (algebraMap A B)).IsElliptic from inferInstance

theorem nonsingular_map_of_equation {K : Type*} [Field K] (𝒪 : ValuationSubring K) {Ω : Type*} [Field Ω]
    (ψ : 𝒪 →+* Ω) (W : WeierstrassCurve 𝒪) [W.IsElliptic] {a b : 𝒪}
    (hab : ((W.map (algebraMap 𝒪 K)).baseChange K).toAffine.Equation (algebraMap 𝒪 K a) (algebraMap 𝒪 K b)) :
    ((W.map ψ).baseChange Ω).toAffine.Nonsingular (ψ a) (ψ b) := by
  have h𝒪 : W.toAffine.Equation a b := by
    have h1 : algebraMap 𝒪 K (W.toAffine.polynomial.evalEval a b) = 0 := by
      rw [← Polynomial.map_mapRingHom_evalEval, ← WeierstrassCurve.Affine.map_polynomial]; exact hab
    exact (map_eq_zero_iff _ (IsFractionRing.injective 𝒪 K)).mp h1
  exact WeierstrassCurve.Affine.equation_iff_nonsingular.mp (h𝒪.map ψ)

theorem natCast_ne_zero_of_isUnit {K : Type*} [Field K] (𝒪 : ValuationSubring K) {n : ℕ}
    (hn : IsUnit ((n : ℕ) : (𝒪 : Type _))) {A : Type*} [CommRing A] [Nontrivial A] (f : 𝒪 →+* A) : (n : A) ≠ 0 := by
  have := (hn.map f).ne_zero
  rwa [map_natCast] at this

theorem main {K : Type u} [Field K] [IsAlgClosed K] [DecidableEq K] (𝒪 : ValuationSubring K)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω] (ψ : 𝒪 →+* Ω)
    (W : WeierstrassCurve 𝒪) [W.IsElliptic] (n : ℕ) (hn : IsUnit ((n : ℕ) : (𝒪 : Type u)))
    (xS yS xT yT : 𝒪)
    (hSK : ((W.map (algebraMap 𝒪 K)).baseChange K).toAffine.Nonsingular (algebraMap 𝒪 K xS) (algebraMap 𝒪 K yS))
    (hTK : ((W.map (algebraMap 𝒪 K)).baseChange K).toAffine.Nonsingular (algebraMap 𝒪 K xT) (algebraMap 𝒪 K yT))
    (hSΩ : ((W.map ψ).baseChange Ω).toAffine.Nonsingular (ψ xS) (ψ yS))
    (hTΩ : ((W.map ψ).baseChange Ω).toAffine.Nonsingular (ψ xT) (ψ yT))
    (hSKn : (n : ℤ) • WeierstrassCurve.Affine.Point.some _ _ hSK = 0)
    (hTKn : (n : ℤ) • WeierstrassCurve.Affine.Point.some _ _ hTK = 0)
    (hSΩn : (n : ℤ) • WeierstrassCurve.Affine.Point.some _ _ hSΩ = 0)
    (hTΩn : (n : ℤ) • WeierstrassCurve.Affine.Point.some _ _ hTΩ = 0) :
    ∃ u : 𝒪, algebraMap 𝒪 K u =
        ((weilPairing0 (W.map (algebraMap 𝒪 K)) K n (WeierstrassCurve.Affine.Point.some _ _ hSK)
          (WeierstrassCurve.Affine.Point.some _ _ hTK) : Kˣ) : K) ∧
      ψ u = ((weilPairing0 (W.map ψ) Ω n (WeierstrassCurve.Affine.Point.some _ _ hSΩ)
          (WeierstrassCurve.Affine.Point.some _ _ hTΩ) : Ωˣ) : Ω) := by
  classical
  have hinj : Function.Injective (algebraMap 𝒪 K) := IsFractionRing.injective 𝒪 K
  have hnK : (n : K) ≠ 0 := natCast_ne_zero_of_isUnit 𝒪 hn (algebraMap 𝒪 K)
  have hnΩ : (n : Ω) ≠ 0 := natCast_ne_zero_of_isUnit 𝒪 hn ψ
  have hnne : n ≠ 0 := fun h => hnK (by rw [h, Nat.cast_zero])
  have hn0 : (n : ℤ) ≠ 0 := by exact_mod_cast hnne
  have hn0' : ((n : ℤ) : (𝒪 : Type u)) ≠ 0 := by rw [Int.cast_natCast]; exact hn.ne_zero

  obtain ⟨u, hu⟩ := exists_algebraMap_eq_weilPairing0 𝒪 (W.map (algebraMap 𝒪 K)) hnK
    (WeierstrassCurve.Affine.Point.some _ _ hSK) (WeierstrassCurve.Affine.Point.some _ _ hTK) hSKn hTKn
  refine ⟨u, hu, ?_⟩

  obtain ⟨pT, qT, cT, cT', hcT, hcT', hTKeq, hTΩeq⟩ :=
    WeierstrassCurve.Affine.exists_smul_basis_eq_algebraMap_mul_weilNum_of_valuationSubring 𝒪 ψ W n hn
      (WeierstrassCurve.Affine.Point.some _ _ hTK) (WeierstrassCurve.Affine.Point.some _ _ hTΩ)
      (Or.inr ⟨xT, yT, hTK, hTΩ, rfl, rfl⟩) hTKn hTΩn
  obtain ⟨pO, qO, cO, cO', hcO, hcO', hOKeq, hOΩeq⟩ :=
    WeierstrassCurve.Affine.exists_smul_basis_eq_algebraMap_mul_weilNum_of_valuationSubring 𝒪 ψ W n hn
      0 0 (Or.inl ⟨rfl, rfl⟩) (smul_zero _) (smul_zero _)

  obtain ⟨v, hv⟩ := hn
  set a : (𝒪 : Type u) := ((v⁻¹ ^ 2 : (𝒪 : Type u)ˣ) : (𝒪 : Type u)) with ha
  set FT : Polynomial 𝒪 := W.Φ n - Polynomial.C xT * W.ΨSq n with hFT
  set FO : Polynomial 𝒪 := Polynomial.C a * W.ΨSq n with hFO
  have hFTm : FT.Monic := monic_Phi_sub W hn0 xT
  have hFOm : FO.Monic := by
    have hlc : (W.ΨSq n).leadingCoeff = (v : (𝒪 : Type u)) ^ 2 := by
      rw [WeierstrassCurve.leadingCoeff_ΨSq W hn0', Int.cast_natCast, hv]
    refine Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one ?_
    rw [hlc, ha, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← mul_pow, inv_mul_cancel, one_pow, Units.val_one]
  obtain ⟨tT, htT⟩ := exists_multiset_prod_eq 𝒪 FT hFTm
  obtain ⟨tO, htO⟩ := exists_multiset_prod_eq 𝒪 FO hFOm
  set B : Finset (IsLocalRing.ResidueField 𝒪) :=
    (tT.map (IsLocalRing.residue 𝒪)).toFinset ∪ (tO.map (IsLocalRing.residue 𝒪)).toFinset ∪
      {IsLocalRing.residue 𝒪 xS} with hB
  obtain ⟨ξ, hξB⟩ := exists_residue_notMem 𝒪 B
  have hresT : ∀ ζ ∈ tT, IsLocalRing.residue 𝒪 ξ ≠ IsLocalRing.residue 𝒪 ζ := by
    intro ζ hζ h; apply hξB
    rw [hB, Finset.mem_union, Finset.mem_union, Multiset.mem_toFinset, h]
    exact Or.inl (Or.inl (Multiset.mem_map_of_mem _ hζ))
  have hresO : ∀ ζ ∈ tO, IsLocalRing.residue 𝒪 ξ ≠ IsLocalRing.residue 𝒪 ζ := by
    intro ζ hζ h; apply hξB
    rw [hB, Finset.mem_union, Finset.mem_union, Multiset.mem_toFinset, Multiset.mem_toFinset, h]
    exact Or.inl (Or.inr (Multiset.mem_map_of_mem _ hζ))
  have hresS : IsLocalRing.residue 𝒪 ξ ≠ IsLocalRing.residue 𝒪 xS := by
    intro h; apply hξB
    rw [hB, Finset.mem_union, h]
    exact Or.inr (Finset.mem_singleton_self _)
  obtain ⟨e', he'⟩ := (isUnit_sub_of_residue_ne 𝒪 hresS).exists_right_inv
  have hxK : algebraMap 𝒪 K ξ ≠ algebraMap 𝒪 K xS := fun h => hresS (by rw [hinj h])
  have hxΩ : ψ ξ ≠ ψ xS := map_ne_of_residue_ne 𝒪 ψ hresS

  have hrootK : ∀ {F : Polynomial 𝒪} {t : Multiset 𝒪}, F = (t.map fun ζ => X - C ζ).prod →
      (∀ ζ ∈ t, IsLocalRing.residue 𝒪 ξ ≠ IsLocalRing.residue 𝒪 ζ) →
      (F.map (algebraMap 𝒪 K)).eval (algebraMap 𝒪 K ξ) ≠ 0 := by
    intro F t hF hres h
    rw [eval_map, eval₂_at_apply, map_eq_zero_iff _ hinj, hF] at h
    exact hres ξ (mem_of_eval_prod_eq_zero 𝒪 h) rfl
  have hrootΩ : ∀ {F : Polynomial 𝒪} {t : Multiset 𝒪}, F.Monic → F = (t.map fun ζ => X - C ζ).prod →
      (∀ ζ ∈ t, IsLocalRing.residue 𝒪 ξ ≠ IsLocalRing.residue 𝒪 ζ) →
      (F.map ψ).eval (ψ ξ) ≠ 0 := by
    intro F t hFm hF hres h
    obtain ⟨ζ, hζ, hζξ⟩ := exists_root_of_eval_map_eq_zero 𝒪 ψ F hFm h
    rw [hF] at hζ
    exact map_ne_of_residue_ne 𝒪 ψ (hres ζ (mem_of_eval_prod_eq_zero 𝒪 hζ)) hζξ.symm
  have hT_K := hrootK htT hresT
  have hO_K := hrootK htO hresO
  have hT_Ω := hrootΩ hFTm htT hresT
  have hO_Ω := hrootΩ hFOm htO hresO

  obtain ⟨ηK, hηK⟩ := exists_nonsingular ((W.map (algebraMap 𝒪 K)).baseChange K) (algebraMap 𝒪 K ξ)
  have hηmem : ηK ∈ 𝒪 := yc_mem_of_xc_mem 𝒪 W hηK.1 ξ.2
  obtain ⟨η, rfl⟩ : ∃ η : 𝒪, algebraMap 𝒪 K η = ηK := ⟨⟨ηK, hηmem⟩, rfl⟩
  have hXK : ((W.map (algebraMap 𝒪 K)).baseChange K).toAffine.Nonsingular (algebraMap 𝒪 K ξ) (algebraMap 𝒪 K η) := hηK
  have hXΩ : ((W.map ψ).baseChange Ω).toAffine.Nonsingular (ψ ξ) (ψ η) := nonsingular_map_of_equation 𝒪 ψ W hXK.1

  have hX1K : (n : ℤ) • WeierstrassCurve.Affine.Point.some _ _ hXK ≠ WeierstrassCurve.Affine.Point.some _ _ hTK := by
    intro h
    have hx := WeierstrassCurve.Affine.Point.zsmul_x_mul_psi_sq ((W.map (algebraMap 𝒪 K)).baseChange K) n hXK hTK h
    rw [WeierstrassCurve.Affine.evalEval_psi_sq _ hXK.1, evalEval_φ _ hXK.1] at hx
    change algebraMap 𝒪 K xT * ((W.map (algebraMap 𝒪 K)).ΨSq n).eval (algebraMap 𝒪 K ξ) =
      ((W.map (algebraMap 𝒪 K)).Φ n).eval (algebraMap 𝒪 K ξ) at hx
    apply hT_K
    rw [hFT, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C, ← WeierstrassCurve.map_Φ,
      ← WeierstrassCurve.map_ΨSq, eval_sub, eval_mul, eval_C, ← hx, sub_self]
  have hX2K : (n : ℤ) • WeierstrassCurve.Affine.Point.some _ _ hXK ≠ 0 := by
    intro h
    have hψn := (WeierstrassCurve.Affine.Point.smul_some_eq_zero_iff ((W.map (algebraMap 𝒪 K)).baseChange K) hXK (n : ℤ)).mp h
    have hΨ : ((W.map (algebraMap 𝒪 K)).ΨSq n).eval (algebraMap 𝒪 K ξ) = 0 := by
      rw [← WeierstrassCurve.Affine.evalEval_psi_sq (W.map (algebraMap 𝒪 K)) hXK.1 n]
      change (((W.map (algebraMap 𝒪 K)).baseChange K).ψ n).evalEval _ _ ^ 2 = 0
      rw [hψn]; ring
    apply hO_K
    rw [hFO, Polynomial.map_mul, Polynomial.map_C, ← WeierstrassCurve.map_ΨSq, eval_mul, eval_C, hΨ, mul_zero]

  have hX1Ω : (n : ℤ) • WeierstrassCurve.Affine.Point.some _ _ hXΩ ≠ WeierstrassCurve.Affine.Point.some _ _ hTΩ := by
    intro h
    have hx := WeierstrassCurve.Affine.Point.zsmul_x_mul_psi_sq ((W.map ψ).baseChange Ω) n hXΩ hTΩ h
    rw [WeierstrassCurve.Affine.evalEval_psi_sq _ hXΩ.1, evalEval_φ _ hXΩ.1] at hx
    change ψ xT * ((W.map ψ).ΨSq n).eval (ψ ξ) = ((W.map ψ).Φ n).eval (ψ ξ) at hx
    apply hT_Ω
    rw [hFT, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C, ← WeierstrassCurve.map_Φ,
      ← WeierstrassCurve.map_ΨSq, eval_sub, eval_mul, eval_C, ← hx, sub_self]
  have hX2Ω : (n : ℤ) • WeierstrassCurve.Affine.Point.some _ _ hXΩ ≠ 0 := by
    intro h
    have hψn := (WeierstrassCurve.Affine.Point.smul_some_eq_zero_iff ((W.map ψ).baseChange Ω) hXΩ (n : ℤ)).mp h
    have hΨ : ((W.map ψ).ΨSq n).eval (ψ ξ) = 0 := by
      rw [← WeierstrassCurve.Affine.evalEval_psi_sq (W.map ψ) hXΩ.1 n]
      change (((W.map ψ).baseChange Ω).ψ n).evalEval _ _ ^ 2 = 0
      rw [hψn]; ring
    apply hO_Ω
    rw [hFO, Polynomial.map_mul, Polynomial.map_C, ← WeierstrassCurve.map_ΨSq, eval_mul, eval_C, hΨ, mul_zero]

  obtain ⟨xZK, yZK, hZK', haddK, h1K, h2K, hidK⟩ :=
    eval_formula (W.map (algebraMap 𝒪 K)) hnK hTKn hSK hSKn hXK hxK hX1K hX2K
  obtain ⟨xZΩ, yZΩ, hZΩ', haddΩ, h1Ω, h2Ω, hidΩ⟩ :=
    eval_formula (W.map ψ) hnΩ hTΩn hSΩ hSΩn hXΩ hxΩ hX1Ω hX2Ω

  obtain ⟨hZK, haddK'⟩ := exists_some_add_some_eq W (algebraMap 𝒪 K)
    (V := (W.map (algebraMap 𝒪 K)).baseChange K) rfl he' hxK hXK hSK
  obtain ⟨hZΩ, haddΩ'⟩ := exists_some_add_some_eq W ψ (V := (W.map ψ).baseChange Ω) rfl he' hxΩ hXΩ hSΩ
  have eqK := haddK.symm.trans haddK'
  have eqΩ := haddΩ.symm.trans haddΩ'
  simp only [WeierstrassCurve.Affine.Point.some.injEq] at eqK eqΩ
  obtain ⟨rfl, rfl⟩ := eqK
  obtain ⟨rfl, rfl⟩ := eqΩ

  set xZ := W.toAffine.addX ξ xS ((η - yS) * e') with hxZ
  set yZ := W.toAffine.addY ξ xS η ((η - yS) * e') with hyZ
  have evK : ∀ (p q : Polynomial 𝒪) {x y : 𝒪}
      (hxy : ((W.map (algebraMap 𝒪 K)).baseChange K).toAffine.Nonsingular (algebraMap 𝒪 K x) (algebraMap 𝒪 K y))
      {c : K} {N : ((W.map (algebraMap 𝒪 K))⁄K).CoordinateRing},
      Polynomial.map (algebraMap 𝒪 K) p • (1 : ((W.map (algebraMap 𝒪 K))⁄K).CoordinateRing) +
          Polynomial.map (algebraMap 𝒪 K) q • CoordinateRing.mk ((W.map (algebraMap 𝒪 K))⁄K) Y =
        algebraMap K _ c * N →
      algebraMap 𝒪 K (p.eval x + q.eval x * y) = c * CoordinateRing.evalAt (W.map (algebraMap 𝒪 K)) K hxy.left N := by
    intro p q x y hxy c N h
    have := congrArg (CoordinateRing.evalAt (W.map (algebraMap 𝒪 K)) K hxy.left) h
    rw [evalAt_smul_basis, eval_map, eval_map, eval₂_at_apply, eval₂_at_apply, ← map_mul, ← map_add,
      map_mul, evalAt_algebraMap] at this
    exact this
  have evΩ : ∀ (p q : Polynomial 𝒪) {x y : 𝒪}
      (hxy : ((W.map ψ).baseChange Ω).toAffine.Nonsingular (ψ x) (ψ y))
      {c : Ω} {N : ((W.map ψ)⁄Ω).CoordinateRing},
      Polynomial.map ψ p • (1 : ((W.map ψ)⁄Ω).CoordinateRing) + Polynomial.map ψ q • CoordinateRing.mk ((W.map ψ)⁄Ω) Y =
        algebraMap Ω _ c * N →
      ψ (p.eval x + q.eval x * y) = c * CoordinateRing.evalAt (W.map ψ) Ω hxy.left N := by
    intro p q x y hxy c N h
    have := congrArg (CoordinateRing.evalAt (W.map ψ) Ω hxy.left) h
    rw [evalAt_smul_basis, eval_map, eval_map, eval₂_at_apply, eval₂_at_apply, ← map_mul, ← map_add,
      map_mul, evalAt_algebraMap] at this
    exact this
  have aTX := evK pT qT hXK hTKeq
  have aTZ := evK pT qT hZK hTKeq
  have aOX := evK pO qO hXK hOKeq
  have aOZ := evK pO qO hZK hOKeq
  have bTX := evΩ pT qT hXΩ hTΩeq
  have bTZ := evΩ pT qT hZΩ hTΩeq
  have bOX := evΩ pO qO hXΩ hOΩeq
  have bOZ := evΩ pO qO hZΩ hOΩeq

  have hK : u * (pT.eval ξ + qT.eval ξ * η) * (pO.eval xZ + qO.eval xZ * yZ) =
      (pT.eval xZ + qT.eval xZ * yZ) * (pO.eval ξ + qO.eval ξ * η) := by
    apply hinj
    rw [map_mul, map_mul, map_mul, hu, aTX, aOZ, aTZ, aOX]
    linear_combination (cT * cO) * hidK

  have hΩ := congrArg ψ hK
  rw [map_mul, map_mul, map_mul, bTX, bOZ, bTZ, bOX] at hΩ

  have hM : cT' * CoordinateRing.evalAt (W.map ψ) Ω hXΩ.left (weilNum (W.map ψ) Ω n (WeierstrassCurve.Affine.Point.some _ _ hTΩ)) *
      (cO' * CoordinateRing.evalAt (W.map ψ) Ω hZΩ.left (weilNum (W.map ψ) Ω n 0)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hcT' h1Ω) (mul_ne_zero hcO' h2Ω)
  apply mul_right_cancel₀ hM
  rw [← mul_assoc, hΩ]
  linear_combination (-(cT' * cO')) * hidΩ

end Main

end P2M.WeilVal
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_exists_algebraMap_eq_weilPairing0_and_map_eq_weilPairing0_of_valuationSubring.P2M P2MW.S_WeierstrassCurve_Affine_exists_algebraMap_eq_weilPairing0_and_map_eq_weilPairing0_of_valuationSubring.P2M.WeilVal"
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_exists_algebraMap_eq_weilPairing0_and_map_eq_weilPairing0_of_valuationSubring.P2M"

open P2M.WeilVal in
theorem solution
    {K : Type u} [Field K] [IsAlgClosed K] [DecidableEq K] (𝒪 : ValuationSubring K)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω] (ψ : 𝒪 →+* Ω)
    (W : WeierstrassCurve 𝒪) [W.IsElliptic] (n : ℕ) (hn : IsUnit ((n : ℕ) : (𝒪 : Type u)))
    (xS yS xT yT : 𝒪)
    (hSK : ((W.map (algebraMap 𝒪 K)).baseChange K).toAffine.Nonsingular (algebraMap 𝒪 K xS) (algebraMap 𝒪 K yS))
    (hTK : ((W.map (algebraMap 𝒪 K)).baseChange K).toAffine.Nonsingular (algebraMap 𝒪 K xT) (algebraMap 𝒪 K yT))
    (hSΩ : ((W.map ψ).baseChange Ω).toAffine.Nonsingular (ψ xS) (ψ yS))
    (hTΩ : ((W.map ψ).baseChange Ω).toAffine.Nonsingular (ψ xT) (ψ yT))
    (hSKn : (n : ℤ) • WeierstrassCurve.Affine.Point.some _ _ hSK = 0)
    (hTKn : (n : ℤ) • WeierstrassCurve.Affine.Point.some _ _ hTK = 0)
    (hSΩn : (n : ℤ) • WeierstrassCurve.Affine.Point.some _ _ hSΩ = 0)
    (hTΩn : (n : ℤ) • WeierstrassCurve.Affine.Point.some _ _ hTΩ = 0) :
    ∃ u : 𝒪, algebraMap 𝒪 K u =
        ((weilPairing0 (W.map (algebraMap 𝒪 K)) K n (WeierstrassCurve.Affine.Point.some _ _ hSK)
          (WeierstrassCurve.Affine.Point.some _ _ hTK) : Kˣ) : K) ∧
      ψ u = ((weilPairing0 (W.map ψ) Ω n (WeierstrassCurve.Affine.Point.some _ _ hSΩ)
          (WeierstrassCurve.Affine.Point.some _ _ hTΩ) : Ωˣ) : Ω) :=
  P2M.WeilVal.main 𝒪 ψ W n hn xS yS xT yT hSK hTK hSΩ hTΩ hSKn hTKn hSΩn hTΩn

end S_WeierstrassCurve_Affine_exists_algebraMap_eq_weilPairing0_and_map_eq_weilPairing0_of_valuationSubring
end P2MW
export P2MW.S_WeierstrassCurve_Affine_exists_algebraMap_eq_weilPairing0_and_map_eq_weilPairing0_of_valuationSubring (solution)
