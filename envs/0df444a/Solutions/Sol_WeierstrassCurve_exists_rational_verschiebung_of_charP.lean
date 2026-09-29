-- Prove2me | solution 1 for WeierstrassCurve.exists_rational_verschiebung_of_charP
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/8466fff9-f059-508a-8d42-87983e2e0b14

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_EllipticCurve_DivisionPolynomialOmega
import Theorems.Thm_WeierstrassCurve_Psi2Sq_mul_wronskian_sq
import Theorems.Thm_WeierstrassCurve_isCoprime_Phi_PsiSq
import Theorems.Thm_WeierstrassCurve_Psi2Sq_ne_zero_of_isElliptic
import Theorems.Thm_WeierstrassCurve_Affine_Point_zsmul_x_mul_psi_sq
import Theorems.Thm_WeierstrassCurve_Affine_Point_zsmul_y_mul_psi_cube
import Theorems.Thm_WeierstrassCurve_two_mul_omega
import Theorems.Thm_WeierstrassCurve_Affine_Point_zsmul_some_eq_some_div
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_rational_verschiebung_of_charP
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine Affine.negY Affine.CoordinateRing.mk_Ψ_sq a₃ a₁ map map_Φ Affine.CoordinateRing mk preΨ Ψ₂Sq a₄ a₂ a₆ Affine.Point.some Affine.Point.some.injEq Affine.CoordinateRing.mk_ψ₂_sq Affine.negAddY ψ_two map_ΨSq ΨSq toAffine Affine.slope_of_Y_ne Affine.Point Affine.CoordinateRing.mk Affine.evalEval_polynomialY Affine.CoordinateRing.mk_ψ ψ₂ natDegree_Φ_pos map_preΨ Affine.CoordinateRing.mk_φ Affine.addY Affine.equation_iff map_Ψ₂Sq Affine.Point.add_self_of_Y_ne baseChange evalEvalBC ψDbl twoω ω ψ_mul_ψDbl Psi2Sq_mul_wronskian_sq isCoprime_Phi_PsiSq Psi2Sq_ne_zero_of_isElliptic Affine.Point.zsmul_x_mul_psi_sq Affine.Point.zsmul_y_mul_psi_cube two_mul_omega Affine.Point.zsmul_some_eq_some_div"
namespace VerschiebungSol
p2m_open "WeierstrassCurve~evalEval_ψ_sq~evalEval_φ"

section Engine

variable {F : Type*} [Field F]

theorem derivative_eq_zero_of_wronskian {A B : F[X]} (hcop : IsCoprime A B)
    (hw : derivative A * B = A * derivative B) : derivative A = 0 ∧ derivative B = 0 := by
  by_cases hA : A = 0
  · subst hA
    have hu : IsUnit B := isCoprime_zero_left.mp hcop
    obtain ⟨r, -, rfl⟩ := Polynomial.isUnit_iff.mp hu
    exact ⟨derivative_zero, derivative_C⟩
  have hdvd : A ∣ derivative A := by
    refine hcop.dvd_of_dvd_mul_right ?_
    exact ⟨derivative B, by rw [hw]⟩
  have hA' : derivative A = 0 :=
    eq_zero_of_dvd_of_degree_lt hdvd (degree_derivative_lt hA)
  refine ⟨hA', ?_⟩
  rw [hA', zero_mul, eq_comm, mul_eq_zero] at hw
  exact hw.resolve_left hA

theorem derivative_Phi_eq_zero (W : WeierstrassCurve F) [W.IsElliptic] {n : ℤ} (hn : (n : F) = 0) :
    derivative (W.Φ n) = 0 ∧ derivative (W.ΨSq n) = 0 := by
  have hcard := WeierstrassCurve.Psi2Sq_mul_wronskian_sq W n
  rw [hn, zero_pow two_ne_zero, C_0, zero_mul, mul_eq_zero] at hcard
  have hw : derivative (W.Φ n) * W.ΨSq n - W.Φ n * derivative (W.ΨSq n) = 0 := by
    rcases hcard with h0 | h0
    · exact absurd h0 (WeierstrassCurve.Psi2Sq_ne_zero_of_isElliptic W)
    · exact (pow_eq_zero_iff two_ne_zero).mp h0
  exact derivative_eq_zero_of_wronskian (WeierstrassCurve.isCoprime_Phi_PsiSq W n)
    (sub_eq_zero.mp hw)

theorem Phi_eq_expand (W : WeierstrassCurve F) [W.IsElliptic] (p : ℕ) [Fact p.Prime] [CharP F p]
    {n : ℤ} (hn : (n : F) = 0) : W.Φ n = expand F p (contract p (W.Φ n)) :=
  (expand_contract p (derivative_Phi_eq_zero W hn).1 (Fact.out : p.Prime).ne_zero).symm

theorem PsiSq_eq_expand (W : WeierstrassCurve F) [W.IsElliptic] (p : ℕ) [Fact p.Prime] [CharP F p]
    {n : ℤ} (hn : (n : F) = 0) : W.ΨSq n = expand F p (contract p (W.ΨSq n)) :=
  (expand_contract p (derivative_Phi_eq_zero W hn).2 (Fact.out : p.Prime).ne_zero).symm

theorem Phi_PsiSq_charP_eq_expand (W : WeierstrassCurve F) [W.IsElliptic] (p : ℕ) [Fact p.Prime]
    [CharP F p] : W.Φ p = expand F p (contract p (W.Φ p)) ∧
      W.ΨSq p = expand F p (contract p (W.ΨSq p)) := by
  have hp : ((p : ℤ) : F) = 0 := by rw [Int.cast_natCast]; exact CharP.cast_eq_zero F p
  exact ⟨Phi_eq_expand W p hp, PsiSq_eq_expand W p hp⟩

theorem two_ne_zero_of_charP {p : ℕ} [Fact p.Prime] [CharP F p] (hp2 : p ≠ 2) : (2 : F) ≠ 0 := by
  intro h2
  have hdvd : p ∣ 2 := by
    have := (CharP.cast_eq_zero_iff F p 2).mp (by exact_mod_cast h2)
    exact this
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact (Fact.out : p.Prime).one_lt.ne' h
  · exact hp2 h

theorem derivative_mul_eq_of_sq_mul_eq (h2 : (2 : F) ≠ 0) {a b A B : F[X]} (hb : b ≠ 0)
    (hB : B ≠ 0) (hA' : derivative A = 0) (hB' : derivative B = 0) (h : a ^ 2 * B = b ^ 2 * A) :
    derivative a * b = a * derivative b := by
  by_cases hA : A = 0
  · rw [hA, mul_zero, mul_eq_zero] at h
    rcases h with h | h
    · rw [(pow_eq_zero_iff two_ne_zero).mp h, derivative_zero, zero_mul, zero_mul]
    · exact absurd h hB
  have hd := congrArg derivative h
  rw [derivative_mul, derivative_mul, hA', hB', mul_zero, add_zero, mul_zero, add_zero,
    derivative_sq, derivative_sq] at hd
  have hd' : a * derivative a * B = b * derivative b * A := by
    have h2C : (C (2 : F)) ≠ 0 := by rwa [Ne, C_eq_zero]
    have := hd
    rw [mul_assoc (C 2), mul_assoc (C 2), mul_assoc (C 2), mul_assoc (C 2)] at this
    exact mul_left_cancel₀ h2C this
  have hkey : (derivative a * b - a * derivative b) * (b ^ 3 * A) = 0 := by
    have e1 : a * derivative b * (b ^ 3 * A) = a * b ^ 2 * (b * derivative b * A) := by ring
    rw [sub_mul, e1, ← hd']
    have e2 : a * b ^ 2 * (a * derivative a * B) = derivative a * b ^ 2 * (a ^ 2 * B) := by ring
    rw [e2, h]
    ring
  rw [mul_eq_zero] at hkey
  rcases hkey with hk | hk
  · exact sub_eq_zero.mp hk
  · rw [mul_eq_zero] at hk
    rcases hk with hk | hk
    · exact absurd ((pow_eq_zero_iff three_ne_zero).mp hk) hb
    · exact absurd hk hA

theorem exists_expand_of_derivative_mul_eq (p : ℕ) [Fact p.Prime] [CharP F p] {a b : F[X]}
    (h : derivative a * b = a * derivative b) :
    ∃ c d : F[X], a * b ^ (p - 1) = expand F p c ∧ b ^ p = expand F p d := by
  have hp : p.Prime := Fact.out
  have hp1 : derivative (a * b ^ (p - 1)) = 0 := by
    obtain ⟨m, hm⟩ : ∃ m, p = m + 2 := ⟨p - 2, (Nat.sub_add_cancel hp.two_le).symm⟩
    have hcast : ((p - 1 : ℕ) : F) = -1 := by
      rw [Nat.cast_sub hp.one_le, CharP.cast_eq_zero F p, Nat.cast_one, zero_sub]
    rw [derivative_mul, derivative_pow, hcast]
    have hpm : p - 1 - 1 = m := by omega
    have hpm' : p - 1 = m + 1 := by omega
    rw [hpm, hpm', pow_succ]
    have : derivative a * (b ^ m * b) + a * (C (-1 : F) * b ^ m * derivative b) =
        b ^ m * (derivative a * b - a * derivative b) := by
      rw [C_neg, C_1]; ring
    rw [this, h, sub_self, mul_zero]
  have hp2 : derivative (b ^ p) = 0 := by
    rw [derivative_pow, CharP.cast_eq_zero F p, C_0, zero_mul, zero_mul]
  exact ⟨contract p (a * b ^ (p - 1)), contract p (b ^ p),
    (expand_contract p hp1 hp.ne_zero).symm, (expand_contract p hp2 hp.ne_zero).symm⟩

theorem exists_expand_of_sq_mul_eq (p : ℕ) [Fact p.Prime] [CharP F p] (hp2 : p ≠ 2)
    {a b A B : F[X]} (hb : b ≠ 0) (hB : B ≠ 0) (hA' : derivative A = 0)
    (hB' : derivative B = 0) (h : a ^ 2 * B = b ^ 2 * A) :
    ∃ c d : F[X], a * b ^ (p - 1) = expand F p c ∧ b ^ p = expand F p d :=
  exists_expand_of_derivative_mul_eq p
    (derivative_mul_eq_of_sq_mul_eq (two_ne_zero_of_charP hp2) hb hB hA' hB' h)

theorem eval_div_eq_of_expand {k : Type*} [Field k] [Algebra F k] (p : ℕ) (hp : 0 < p)
    {a b c d : F[X]} (hc : a * b ^ (p - 1) = expand F p c) (hd : b ^ p = expand F p d) {x : k}
    (hx : (b.map (algebraMap F k)).eval x ≠ 0) :
    (d.map (algebraMap F k)).eval (x ^ p) ≠ 0 ∧
      (a.map (algebraMap F k)).eval x / (b.map (algebraMap F k)).eval x =
        (c.map (algebraMap F k)).eval (x ^ p) / (d.map (algebraMap F k)).eval (x ^ p) := by
  have hd' : (b.map (algebraMap F k)).eval x ^ p = (d.map (algebraMap F k)).eval (x ^ p) := by
    rw [← eval_pow, ← Polynomial.map_pow, hd, map_expand, expand_eval]
  have hc' : (a.map (algebraMap F k)).eval x * (b.map (algebraMap F k)).eval x ^ (p - 1) =
      (c.map (algebraMap F k)).eval (x ^ p) := by
    rw [← eval_pow, ← Polynomial.map_pow, ← eval_mul, ← Polynomial.map_mul, hc, map_expand,
      expand_eval]
  have hdne : (d.map (algebraMap F k)).eval (x ^ p) ≠ 0 := by
    rw [← hd']; exact pow_ne_zero _ hx
  refine ⟨hdne, ?_⟩
  rw [div_eq_div_iff hx hdne, ← hd', ← hc']
  obtain ⟨m, hm⟩ : ∃ m, p = m + 1 := ⟨p - 1, (Nat.sub_add_cancel hp).symm⟩
  rw [hm, Nat.add_sub_cancel, pow_succ]
  ring

theorem ΨSq_ne_zero_of_ne_zero (W : WeierstrassCurve F) [W.IsElliptic] {n : ℤ} (hn : n ≠ 0) :
    W.ΨSq n ≠ 0 := by
  intro h0
  have hcop := WeierstrassCurve.isCoprime_Phi_PsiSq W n
  rw [h0, isCoprime_zero_right] at hcop
  exact (W.natDegree_Φ_pos hn).ne' (natDegree_eq_zero_of_isUnit hcop)

theorem preΨ_ne_zero_of_ne_zero (W : WeierstrassCurve F) [W.IsElliptic] {n : ℤ} (hn : n ≠ 0) :
    W.preΨ n ≠ 0 := by
  intro h0
  apply ΨSq_ne_zero_of_ne_zero W hn
  rw [WeierstrassCurve.ΨSq, h0, zero_pow two_ne_zero, zero_mul]

theorem exists_expand_odd (W : WeierstrassCurve F) [W.IsElliptic] (p : ℕ) [Fact p.Prime]
    [CharP F p] {m : ℕ} (hm : p = 2 * m + 1) :
    ∃ c d : F[X], W.preΨ (2 * p) * (W.preΨ p ^ 4 * W.Ψ₂Sq ^ m) ^ (p - 1) = expand F p c ∧
      (W.preΨ p ^ 4 * W.Ψ₂Sq ^ m) ^ p = expand F p d := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by omega
  have hpF : (p : F) = 0 := CharP.cast_eq_zero F p
  have hp0 : (p : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hp.ne_zero
  have h2p0 : 2 * (p : ℤ) ≠ 0 := mul_ne_zero two_ne_zero hp0
  have hb : W.preΨ p ^ 4 * W.Ψ₂Sq ^ m ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (preΨ_ne_zero_of_ne_zero W hp0))
      (pow_ne_zero _ (WeierstrassCurve.Psi2Sq_ne_zero_of_isElliptic W))
  have hB : W.ΨSq p ^ 4 * W.Ψ₂Sq ^ p ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (ΨSq_ne_zero_of_ne_zero W hp0))
      (pow_ne_zero _ (WeierstrassCurve.Psi2Sq_ne_zero_of_isElliptic W))
  have hΨp' : derivative (W.ΨSq p) = 0 :=
    (derivative_Phi_eq_zero W (n := p) (by rw [Int.cast_natCast]; exact hpF)).2
  have hA' : derivative (W.ΨSq (2 * p)) = 0 :=
    (derivative_Phi_eq_zero W (n := 2 * p)
      (by rw [Int.cast_mul, Int.cast_natCast, hpF, mul_zero])).2
  have hB' : derivative (W.ΨSq p ^ 4 * W.Ψ₂Sq ^ p) = 0 := by
    rw [derivative_mul, derivative_pow, hΨp', mul_zero, zero_mul, zero_add, derivative_pow, hpF,
      C_0, zero_mul, zero_mul, mul_zero]
  have h : W.preΨ (2 * p) ^ 2 * (W.ΨSq p ^ 4 * W.Ψ₂Sq ^ p) =
      (W.preΨ p ^ 4 * W.Ψ₂Sq ^ m) ^ 2 * W.ΨSq (2 * p) := by
    have hev : Even (2 * (p : ℤ)) := even_two_mul _
    have hod : ¬ Even (p : ℤ) := by
      rw [Int.not_even_iff_odd, Int.odd_coe_nat]; exact ⟨m, hm⟩
    have e1 : W.ΨSq p = W.preΨ p ^ 2 := by
      rw [WeierstrassCurve.ΨSq, if_neg hod, mul_one]
    have e2 : W.ΨSq (2 * p) = W.preΨ (2 * p) ^ 2 * W.Ψ₂Sq := by
      rw [WeierstrassCurve.ΨSq, if_pos hev]
    have e3 : W.Ψ₂Sq ^ p = (W.Ψ₂Sq ^ m) ^ 2 * W.Ψ₂Sq := by
      rw [hm, pow_succ, pow_mul']
    rw [e1, e2, e3]
    ring
  exact exists_expand_of_sq_mul_eq p hp2 hb hB hA' hB' h

end Engine

section Pointwise

variable {K : Type*} [Field K]

theorem evalEval_eq_of_mk_eq (E : WeierstrassCurve K) {a b : K[X][Y]}
    (hab : Affine.CoordinateRing.mk E a = Affine.CoordinateRing.mk E b) {x y : K}
    (hxy : E.toAffine.Equation x y) : a.evalEval x y = b.evalEval x y := by
  obtain ⟨q, hq⟩ := AdjoinRoot.mk_eq_mk.mp hab
  have h0 : (a - b).evalEval x y = 0 := by
    rw [hq, evalEval_mul, (show E.toAffine.polynomial.evalEval x y = 0 from hxy), zero_mul]
  rwa [evalEval_sub, sub_eq_zero] at h0

theorem evalEval_ψ_sq (E : WeierstrassCurve K) (n : ℤ) {x y : K} (hxy : E.toAffine.Equation x y) :
    (E.ψ n).evalEval x y ^ 2 = (E.ΨSq n).eval x := by
  have hmk : Affine.CoordinateRing.mk E (E.ψ n ^ 2) =
      Affine.CoordinateRing.mk E (C (E.ΨSq n)) := by
    rw [map_pow, Affine.CoordinateRing.mk_ψ, Affine.CoordinateRing.mk_Ψ_sq]
  rw [← evalEval_pow, evalEval_eq_of_mk_eq E hmk hxy, evalEval_C]

theorem evalEval_φ (E : WeierstrassCurve K) (n : ℤ) {x y : K} (hxy : E.toAffine.Equation x y) :
    (E.φ n).evalEval x y = (E.Φ n).eval x := by
  rw [evalEval_eq_of_mk_eq E (Affine.CoordinateRing.mk_φ (W := E) n) hxy, evalEval_C]

theorem evalEval_ψ₂ (E : WeierstrassCurve K) (x y : K) :
    E.ψ₂.evalEval x y = 2 * y + E.a₁ * x + E.a₃ :=
  Affine.evalEval_polynomialY ..

theorem evalEval_ψ₂_sq (E : WeierstrassCurve K) {x y : K} (hxy : E.toAffine.Equation x y) :
    E.ψ₂.evalEval x y ^ 2 = E.Ψ₂Sq.eval x := by
  rw [← evalEval_pow, evalEval_eq_of_mk_eq E _ hxy, evalEval_C]
  rw [map_pow, Affine.CoordinateRing.mk_ψ₂_sq]

theorem evalEval_ψ_of_not_even (E : WeierstrassCurve K) {n : ℤ} (hn : ¬ Even n) {x y : K}
    (hxy : E.toAffine.Equation x y) : (E.ψ n).evalEval x y = (E.preΨ n).eval x := by
  rw [evalEval_eq_of_mk_eq E (Affine.CoordinateRing.mk_ψ (W := E) n) hxy, WeierstrassCurve.Ψ,
    if_neg hn, mul_one, evalEval_C]

theorem evalEval_ψ_of_even (E : WeierstrassCurve K) {n : ℤ} (hn : Even n) {x y : K}
    (hxy : E.toAffine.Equation x y) :
    (E.ψ n).evalEval x y = (E.preΨ n).eval x * E.ψ₂.evalEval x y := by
  rw [evalEval_eq_of_mk_eq E (Affine.CoordinateRing.mk_ψ (W := E) n) hxy, WeierstrassCurve.Ψ,
    if_pos hn, evalEval_mul, evalEval_C]

theorem ψ₂_zsmul_mul_ψ_pow_four [DecidableEq K] (E : WeierstrassCurve K) [E.IsElliptic] (n : ℤ)
    {x y : K} (h : E.toAffine.Nonsingular x y) {x' y' : K} (h' : E.toAffine.Nonsingular x' y')
    (hn : n • Affine.Point.some x y h = Affine.Point.some x' y' h') :
    (2 * y' + E.a₁ * x' + E.a₃) * (E.ψ n).evalEval x y ^ 4 = (E.ψ (2 * n)).evalEval x y := by
  have hx := Affine.Point.zsmul_x_mul_psi_sq E n h h' hn
  have hy := Affine.Point.zsmul_y_mul_psi_cube E n h h' hn
  have hω : 2 * (E.ω n).evalEval x y = (E.ψDbl n).evalEval x y -
      (E.ψ n).evalEval x y * (E.a₁ * (E.φ n).evalEval x y + E.a₃ * (E.ψ n).evalEval x y ^ 2) := by
    have h2 : (2 : K[X][Y]).evalEval x y = 2 := by rw [← coe_evalEvalRingHom, map_ofNat]
    have := congrArg (evalEval x y) (WeierstrassCurve.two_mul_omega E n)
    rw [evalEval_mul, h2, twoω, evalEval_sub,
      evalEval_mul, evalEval_add, evalEval_mul, evalEval_mul, evalEval_C, evalEval_C, eval_C, eval_C,
      evalEval_pow] at this
    exact this
  have hD : (E.ψ n).evalEval x y * (E.ψDbl n).evalEval x y = (E.ψ (2 * n)).evalEval x y := by
    rw [← evalEval_mul, ψ_mul_ψDbl]
  linear_combination (2 * (E.ψ n).evalEval x y) * hy + (E.a₁ * (E.ψ n).evalEval x y ^ 2) * hx +
    (E.ψ n).evalEval x y * hω + hD

theorem exists_some_eq {E : WeierstrassCurve K} {P : E.toAffine.Point} {x₁ y₁ : K}
    {h₁ : E.toAffine.Nonsingular x₁ y₁} (hP : P = Affine.Point.some x₁ y₁ h₁) {x₂ y₂ : K}
    (hx : x₁ = x₂) (hy : y₁ = y₂) :
    ∃ h₂ : E.toAffine.Nonsingular x₂ y₂, P = Affine.Point.some x₂ y₂ h₂ := by
  subst hx hy
  exact ⟨h₁, hP⟩

end Pointwise

section BaseChange

variable {F : Type*} [Field F] (k : Type*) [Field k] [Algebra F k] (W : WeierstrassCurve F)

theorem evalEvalBC_C (q : F[X]) (u v : k) :
    evalEvalBC k (C q) u v = (q.map (algebraMap F k)).eval u := by
  rw [WeierstrassCurve.evalEvalBC, Polynomial.map_C, coe_mapRingHom, evalEval_C]

theorem baseChange_a₁ : (W.baseChange k).a₁ = algebraMap F k W.a₁ := rfl
theorem baseChange_a₂ : (W.baseChange k).a₂ = algebraMap F k W.a₂ := rfl
theorem baseChange_a₃ : (W.baseChange k).a₃ = algebraMap F k W.a₃ := rfl
theorem baseChange_a₄ : (W.baseChange k).a₄ = algebraMap F k W.a₄ := rfl
theorem baseChange_a₆ : (W.baseChange k).a₆ = algebraMap F k W.a₆ := rfl

theorem eval_baseChange_preΨ (n : ℤ) (x : k) :
    ((W.baseChange k).preΨ n).eval x = ((W.preΨ n).map (algebraMap F k)).eval x := by
  rw [show (W.baseChange k).preΨ n = (W.preΨ n).map (algebraMap F k) from W.map_preΨ _ n]

theorem eval_baseChange_ΨSq (n : ℤ) (x : k) :
    ((W.baseChange k).ΨSq n).eval x = ((W.ΨSq n).map (algebraMap F k)).eval x := by
  rw [show (W.baseChange k).ΨSq n = (W.ΨSq n).map (algebraMap F k) from W.map_ΨSq _ n]

theorem eval_baseChange_Φ (n : ℤ) (x : k) :
    ((W.baseChange k).Φ n).eval x = ((W.Φ n).map (algebraMap F k)).eval x := by
  rw [show (W.baseChange k).Φ n = (W.Φ n).map (algebraMap F k) from W.map_Φ _ n]

theorem eval_baseChange_Ψ₂Sq (x : k) :
    (W.baseChange k).Ψ₂Sq.eval x = (W.Ψ₂Sq.map (algebraMap F k)).eval x := by
  rw [show (W.baseChange k).Ψ₂Sq = W.Ψ₂Sq.map (algebraMap F k) from W.map_Ψ₂Sq _]

theorem eval_map_expand (p : ℕ) {A c : F[X]} (hA : A = expand F p c) (x : k) :
    (A.map (algebraMap F k)).eval x = (c.map (algebraMap F k)).eval (x ^ p) := by
  rw [hA, map_expand, expand_eval]

end BaseChange

section Main

variable {F : Type*} [Field F] (p : ℕ) [Fact p.Prime] (k : Type*) [Field k] [Algebra F k]
  (W : WeierstrassCurve F) [W.IsElliptic]

scoped instance baseChange_isElliptic : (W.baseChange k).IsElliptic :=
  inferInstanceAs ((W.map (algebraMap F k)).IsElliptic)

omit [Fact p.Prime] [W.IsElliptic] in

theorem pointwise_common {x y : k} (h : (W.baseChange k).toAffine.Nonsingular x y)
    (hxB : x ∉ {x : k | ((W.ΨSq p * W.Ψ₂Sq).map (algebraMap F k)).IsRoot x}) :
    ((W.ΨSq p).map (algebraMap F k)).eval x ≠ 0 ∧
    (W.Ψ₂Sq.map (algebraMap F k)).eval x ≠ 0 ∧
    (W.baseChange k).toAffine.Equation x y ∧
    ((W.baseChange k).ψ p).evalEval x y ≠ 0 := by
  have hxB' : ((W.ΨSq p).map (algebraMap F k)).eval x ≠ 0 ∧
      (W.Ψ₂Sq.map (algebraMap F k)).eval x ≠ 0 := by
    simpa only [Set.mem_setOf_eq, IsRoot.def, Polynomial.map_mul, eval_mul, mul_eq_zero,
      not_or] using hxB
  refine ⟨hxB'.1, hxB'.2, h.1, ?_⟩
  intro h0
  have := evalEval_ψ_sq (W.baseChange k) p h.1
  rw [h0, eval_baseChange_ΨSq] at this
  exact hxB'.1 (by rw [← this, zero_pow two_ne_zero])

theorem finite_exceptional :
    {x : k | ((W.ΨSq p * W.Ψ₂Sq).map (algebraMap F k)).IsRoot x}.Finite := by
  refine Polynomial.finite_setOf_isRoot ?_
  have hp : p.Prime := Fact.out
  exact (Polynomial.map_ne_zero_iff (algebraMap F k).injective).mpr
    (mul_ne_zero (ΨSq_ne_zero_of_ne_zero W (Int.natCast_ne_zero.mpr hp.ne_zero))
      (WeierstrassCurve.Psi2Sq_ne_zero_of_isElliptic W))

variable [CharP F p] [DecidableEq k]

theorem main_odd (hp2 : p ≠ 2) : ∃ (nX dX nY dY : F[X][Y]) (B : Set k), B.Finite ∧
    ∀ (x y : k) (h : (W.baseChange k).toAffine.Nonsingular x y), x ∉ B →
      evalEvalBC k dX (x ^ p) (y ^ p) ≠ 0 ∧ evalEvalBC k dY (x ^ p) (y ^ p) ≠ 0 ∧
      ∃ h', p • Affine.Point.some x y h = Affine.Point.some
        (evalEvalBC k nX (x ^ p) (y ^ p) / evalEvalBC k dX (x ^ p) (y ^ p))
        (evalEvalBC k nY (x ^ p) (y ^ p) / evalEvalBC k dY (x ^ p) (y ^ p)) h' := by
  have hp : p.Prime := Fact.out
  obtain ⟨m, hm⟩ : ∃ m, p = 2 * m + 1 := hp.odd_of_ne_two hp2
  haveI : CharP k p := charP_of_injective_algebraMap (algebraMap F k).injective p
  obtain ⟨hΦ, hΨ⟩ := Phi_PsiSq_charP_eq_expand W p
  obtain ⟨c, d, hc, hd⟩ := exists_expand_odd W p hm
  refine ⟨C (contract p (W.Φ p)), C (contract p (W.ΨSq p)),
    C (c * contract p (W.ΨSq p)) *
        (C (C ((2 : F) ^ p)) * Y + C (C (W.a₁ ^ p) * X + C (W.a₃ ^ p))) -
      C (C W.a₁ * contract p (W.Φ p) * d + C W.a₃ * contract p (W.ΨSq p) * d),
    C (C (2 : F) * d * contract p (W.ΨSq p)),
    {x : k | ((W.ΨSq p * W.Ψ₂Sq).map (algebraMap F k)).IsRoot x},
    finite_exceptional p k W, ?_⟩
  intro x y h hxB
  obtain ⟨hΨx, hΨ₂x, heq, hψ⟩ := pointwise_common p k W h hxB

  obtain ⟨y', h', hmul⟩ :=
    Affine.Point.zsmul_some_eq_some_div (W.baseChange k) h (n := p) hψ
  have hkey := ψ₂_zsmul_mul_ψ_pow_four (W.baseChange k) p h h' hmul
  have hev : Even (2 * (p : ℤ)) := even_two_mul _
  have hod : ¬ Even (p : ℤ) := by
    rw [Int.not_even_iff_odd, Int.odd_coe_nat]; exact ⟨m, hm⟩
  rw [evalEval_ψ_of_not_even _ hod heq, evalEval_ψ_of_even _ hev heq, eval_baseChange_preΨ,
    eval_baseChange_preΨ, baseChange_a₁, baseChange_a₃] at hkey
  have eψ2 : (W.baseChange k).ψ₂.evalEval x y =
      2 * y + algebraMap F k W.a₁ * x + algebraMap F k W.a₃ := by
    rw [evalEval_ψ₂, baseChange_a₁, baseChange_a₃]
  have eψ2sq : (W.baseChange k).ψ₂.evalEval x y ^ 2 = (W.Ψ₂Sq.map (algebraMap F k)).eval x := by
    rw [evalEval_ψ₂_sq _ heq, eval_baseChange_Ψ₂Sq]
  generalize (W.baseChange k).ψ₂.evalEval x y = ψ2 at hkey eψ2 eψ2sq

  have ex₁ : ((W.baseChange k).Φ p).eval x / ((W.baseChange k).ΨSq p).eval x =
      ((contract p (W.Φ p)).map (algebraMap F k)).eval (x ^ p) /
        ((contract p (W.ΨSq p)).map (algebraMap F k)).eval (x ^ p) := by
    rw [eval_baseChange_Φ, eval_baseChange_ΨSq, eval_map_expand k p hΦ, eval_map_expand k p hΨ]
  generalize ((W.baseChange k).Φ p).eval x / ((W.baseChange k).ΨSq p).eval x = x₁ at h' hmul hkey ex₁
  have hΨx' : ((contract p (W.ΨSq p)).map (algebraMap F k)).eval (x ^ p) ≠ 0 := by
    rw [← eval_map_expand k p hΨ]; exact hΨx

  obtain ⟨Φx, eΦx⟩ : ∃ t, ((contract p (W.Φ p)).map (algebraMap F k)).eval (x ^ p) = t := ⟨_, rfl⟩
  obtain ⟨Ψx, eΨx⟩ : ∃ t, ((contract p (W.ΨSq p)).map (algebraMap F k)).eval (x ^ p) = t :=
    ⟨_, rfl⟩
  obtain ⟨cx, ecx⟩ : ∃ t, (c.map (algebraMap F k)).eval (x ^ p) = t := ⟨_, rfl⟩
  obtain ⟨dx, edx⟩ : ∃ t, (d.map (algebraMap F k)).eval (x ^ p) = t := ⟨_, rfl⟩
  rw [eΦx, eΨx] at ex₁
  rw [eΨx] at hΨx'
  have hxΦ : x₁ * Ψx = Φx := by rw [ex₁]; exact div_mul_cancel₀ _ hΨx'

  have hprex : ((W.preΨ p).map (algebraMap F k)).eval x ≠ 0 := by
    intro h0; apply hΨx
    rw [WeierstrassCurve.ΨSq, if_neg hod, mul_one, Polynomial.map_pow, eval_pow, h0,
      zero_pow two_ne_zero]
  have hbx : ((W.preΨ p ^ 4 * W.Ψ₂Sq ^ m).map (algebraMap F k)).eval x =
      ((W.preΨ p).map (algebraMap F k)).eval x ^ 4 *
        (W.Ψ₂Sq.map (algebraMap F k)).eval x ^ m := by
    rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_pow, eval_mul, eval_pow, eval_pow]
  have hbne : ((W.preΨ p ^ 4 * W.Ψ₂Sq ^ m).map (algebraMap F k)).eval x ≠ 0 := by
    rw [hbx]; exact mul_ne_zero (pow_ne_zero _ hprex) (pow_ne_zero _ hΨ₂x)
  obtain ⟨hdx, hquot⟩ := eval_div_eq_of_expand (k := k) p hp.pos hc hd hbne
  rw [edx] at hdx
  rw [ecx, edx, div_eq_div_iff hbne hdx] at hquot

  have hs : (2 * y' + algebraMap F k W.a₁ * x₁ + algebraMap F k W.a₃) *
      ((W.preΨ p ^ 4 * W.Ψ₂Sq ^ m).map (algebraMap F k)).eval x =
      ((W.preΨ (2 * p)).map (algebraMap F k)).eval x * ψ2 ^ p := by
    have e3 : ψ2 ^ p = (ψ2 ^ 2) ^ m * ψ2 := by rw [← pow_mul, ← pow_succ, ← hm]
    rw [hbx, e3, eψ2sq]
    linear_combination ((W.Ψ₂Sq.map (algebraMap F k)).eval x ^ m) * hkey
  have hs' : (2 * y' + algebraMap F k W.a₁ * x₁ + algebraMap F k W.a₃) * dx = cx * ψ2 ^ p := by
    refine mul_right_cancel₀ hbne ?_
    linear_combination dx * hs + ψ2 ^ p * hquot

  have hT : ψ2 ^ p = algebraMap F k (2 ^ p) * y ^ p +
      (algebraMap F k (W.a₁ ^ p) * x ^ p + algebraMap F k (W.a₃ ^ p)) := by
    rw [map_pow, map_pow, map_pow, map_ofNat, eψ2, add_pow_char, add_pow_char, mul_pow, mul_pow,
      add_assoc]
  have h2 : (2 : k) ≠ 0 := two_ne_zero_of_charP hp2

  have edX : evalEvalBC k (C (contract p (W.ΨSq p))) (x ^ p) (y ^ p) = Ψx := by
    rw [evalEvalBC_C, eΨx]
  have enX : evalEvalBC k (C (contract p (W.Φ p))) (x ^ p) (y ^ p) = Φx := by
    rw [evalEvalBC_C, eΦx]
  have edY : evalEvalBC k (C (C (2 : F) * d * contract p (W.ΨSq p))) (x ^ p) (y ^ p) =
      2 * dx * Ψx := by
    rw [evalEvalBC_C, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C, eval_mul, eval_mul,
      eval_C, map_ofNat, edx, eΨx]
  have hdY : (2 : k) * dx * Ψx ≠ 0 := mul_ne_zero (mul_ne_zero h2 hdx) hΨx'
  refine ⟨by rw [edX]; exact hΨx', by rw [edY]; exact hdY, ?_⟩
  refine exists_some_eq (by rw [← natCast_zsmul]; exact hmul) ?_ ?_
  · rw [enX, edX, ex₁]
  · rw [edY, eq_div_iff hdY]
    simp only [WeierstrassCurve.evalEvalBC, Polynomial.map_add, Polynomial.map_sub,
      Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X, coe_mapRingHom, evalEval_add,
      evalEval_sub, evalEval_mul, evalEval_C, evalEval_X, eval_add, eval_mul, eval_C, eval_X]
    rw [eΦx, eΨx, ecx, edx]
    linear_combination Ψx * hs' + (cx * Ψx) * hT - (algebraMap F k W.a₁ * dx) * hxΦ

theorem main_two (hp2 : p = 2) : ∃ (nX dX nY dY : F[X][Y]) (B : Set k), B.Finite ∧
    ∀ (x y : k) (h : (W.baseChange k).toAffine.Nonsingular x y), x ∉ B →
      evalEvalBC k dX (x ^ p) (y ^ p) ≠ 0 ∧ evalEvalBC k dY (x ^ p) (y ^ p) ≠ 0 ∧
      ∃ h', p • Affine.Point.some x y h = Affine.Point.some
        (evalEvalBC k nX (x ^ p) (y ^ p) / evalEvalBC k dX (x ^ p) (y ^ p))
        (evalEvalBC k nY (x ^ p) (y ^ p) / evalEvalBC k dY (x ^ p) (y ^ p)) h' := by
  subst hp2
  haveI : CharP k 2 := charP_of_injective_algebraMap (algebraMap F k).injective 2
  obtain ⟨hΦ, hΨ⟩ := Phi_PsiSq_charP_eq_expand W 2
  refine ⟨C (contract 2 (W.Φ (2 : ℕ))), C (contract 2 (W.ΨSq (2 : ℕ))),
    C (contract 2 (W.Φ (2 : ℕ))) * (C (C W.a₁) * Y +
        C (C (W.a₃ + W.a₁ ^ 3 + W.a₁ * W.a₂) * X +
          C (W.a₃ * W.a₄ + W.a₁ * W.a₃ ^ 2 + W.a₁ * W.a₆))) +
      C (contract 2 (W.ΨSq (2 : ℕ))) * (C (C W.a₃) * Y + C (C W.a₁ * X ^ 2 +
        C (W.a₁ * W.a₄ + W.a₁ ^ 2 * W.a₃ + W.a₂ * W.a₃) * X + C (W.a₃ ^ 3 + W.a₃ * W.a₆))),
    C (contract 2 (W.ΨSq (2 : ℕ)) * (C (W.a₁ ^ 2) * X + C (W.a₃ ^ 2))),
    {x : k | ((W.ΨSq (2 : ℕ) * W.Ψ₂Sq).map (algebraMap F k)).IsRoot x},
    finite_exceptional 2 k W, ?_⟩
  intro x y h hxB
  obtain ⟨hΨx, hΨ₂x, heq, hψ⟩ := pointwise_common 2 k W h hxB
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero

  have hψ2 : algebraMap F k W.a₁ * x + algebraMap F k W.a₃ ≠ 0 := by
    intro h0; apply hψ
    rw [show (W.baseChange k).ψ ((2 : ℕ) : ℤ) = (W.baseChange k).ψ₂ from (W.baseChange k).ψ_two,
      evalEval_ψ₂, baseChange_a₁, baseChange_a₃]
    linear_combination h0 + y * h2

  obtain ⟨y', h', hmul⟩ :=
    Affine.Point.zsmul_some_eq_some_div (W.baseChange k) h (n := (2 : ℕ)) hψ
  have hyne : y ≠ (W.baseChange k).toAffine.negY x y := by
    intro h0; apply hψ2
    rw [Affine.negY, baseChange_a₁, baseChange_a₃] at h0
    linear_combination h0 - y * h2
  have hL := Affine.slope_of_Y_ne (W := (W.baseChange k).toAffine) rfl hyne
  have hden : y - (W.baseChange k).toAffine.negY x y ≠ 0 := sub_ne_zero.mpr hyne
  rw [Affine.negY, baseChange_a₁, baseChange_a₂, baseChange_a₃, baseChange_a₄] at hL
  rw [Affine.negY, baseChange_a₁, baseChange_a₃] at hden
  have hcmp := hmul
  rw [natCast_zsmul, two_nsmul, Affine.Point.add_self_of_Y_ne (h₁ := h) hyne,
    Affine.Point.some.injEq] at hcmp
  obtain ⟨hX1, hY1⟩ := hcmp
  simp only [Affine.addY, Affine.negAddY, Affine.negY] at hY1
  rw [hX1, baseChange_a₁, baseChange_a₃] at hY1
  generalize (W.baseChange k).toAffine.slope x x y y = L at hL hY1
  have hL' : L * (y - (-y - algebraMap F k W.a₁ * x - algebraMap F k W.a₃)) =
      3 * x ^ 2 + 2 * algebraMap F k W.a₂ * x + algebraMap F k W.a₄ - algebraMap F k W.a₁ * y := by
    rw [hL]; exact div_mul_cancel₀ _ hden

  have ex₁ : ((W.baseChange k).Φ (2 : ℕ)).eval x / ((W.baseChange k).ΨSq (2 : ℕ)).eval x =
      ((contract 2 (W.Φ (2 : ℕ))).map (algebraMap F k)).eval (x ^ 2) /
        ((contract 2 (W.ΨSq (2 : ℕ))).map (algebraMap F k)).eval (x ^ 2) := by
    rw [eval_baseChange_Φ, eval_baseChange_ΨSq, eval_map_expand k 2 hΦ, eval_map_expand k 2 hΨ]
  generalize ((W.baseChange k).Φ (2 : ℕ)).eval x / ((W.baseChange k).ΨSq (2 : ℕ)).eval x = x₁
    at h' hmul hY1 ex₁
  have hΨx' : ((contract 2 (W.ΨSq (2 : ℕ))).map (algebraMap F k)).eval (x ^ 2) ≠ 0 := by
    rw [← eval_map_expand k 2 hΨ]; exact hΨx
  obtain ⟨Φx, eΦx⟩ : ∃ t, ((contract 2 (W.Φ (2 : ℕ))).map (algebraMap F k)).eval (x ^ 2) = t :=
    ⟨_, rfl⟩
  obtain ⟨Ψx, eΨx⟩ : ∃ t, ((contract 2 (W.ΨSq (2 : ℕ))).map (algebraMap F k)).eval (x ^ 2) = t :=
    ⟨_, rfl⟩
  rw [eΦx, eΨx] at ex₁
  rw [eΨx] at hΨx'
  have hxΦ : x₁ * Ψx = Φx := by rw [ex₁]; exact div_mul_cancel₀ _ hΨx'

  have heq' : y ^ 2 + algebraMap F k W.a₁ * x * y + algebraMap F k W.a₃ * y =
      x ^ 3 + algebraMap F k W.a₂ * x ^ 2 + algebraMap F k W.a₄ * x + algebraMap F k W.a₆ := by
    have := (Affine.equation_iff x y).mp heq
    rwa [baseChange_a₁, baseChange_a₂, baseChange_a₃, baseChange_a₄, baseChange_a₆] at this

  have hD : algebraMap F k W.a₁ ^ 2 * x ^ 2 + algebraMap F k W.a₃ ^ 2 =
      (algebraMap F k W.a₁ * x + algebraMap F k W.a₃) ^ 2 := by
    linear_combination (-(algebraMap F k W.a₁ * x * algebraMap F k W.a₃)) * h2
  have hdY : Ψx * (algebraMap F k W.a₁ ^ 2 * x ^ 2 + algebraMap F k W.a₃ ^ 2) ≠ 0 := by
    rw [hD]; exact mul_ne_zero hΨx' (pow_ne_zero _ hψ2)
  have edX : evalEvalBC k (C (contract 2 (W.ΨSq (2 : ℕ)))) (x ^ 2) (y ^ 2) = Ψx := by
    rw [evalEvalBC_C, eΨx]
  have enX : evalEvalBC k (C (contract 2 (W.Φ (2 : ℕ)))) (x ^ 2) (y ^ 2) = Φx := by
    rw [evalEvalBC_C, eΦx]
  have edY : evalEvalBC k (C (contract 2 (W.ΨSq (2 : ℕ)) * (C (W.a₁ ^ 2) * X + C (W.a₃ ^ 2))))
      (x ^ 2) (y ^ 2) = Ψx * (algebraMap F k W.a₁ ^ 2 * x ^ 2 + algebraMap F k W.a₃ ^ 2) := by
    rw [evalEvalBC_C]
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.map_X, eval_add, eval_mul, eval_C, eval_X]
    rw [eΨx, map_pow, map_pow]
  refine ⟨by rw [edX]; exact hΨx', by rw [edY]; exact hdY, ?_⟩
  refine exists_some_eq hmul ?_ ?_
  · rw [enX, edX, ex₁]
  · rw [edY, eq_div_iff hdY]
    simp only [WeierstrassCurve.evalEvalBC, Polynomial.map_add, Polynomial.map_mul,
      Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X, coe_mapRingHom, evalEval_add,
      evalEval_mul, evalEval_C, evalEval_X, eval_add, eval_mul, eval_pow, eval_C,
      eval_X]
    rw [eΦx, eΨx]
    simp only [map_add, map_mul, map_pow]
    linear_combination
      (-(Ψx * (algebraMap F k W.a₁ ^ 2 * x ^ 2 + algebraMap F k W.a₃ ^ 2))) * hY1 +
      (Ψx * (-(x₁ - x) * (algebraMap F k W.a₁ * x + algebraMap F k W.a₃))) * hL' +
      (Ψx * (algebraMap F k W.a₁ * x₁ + algebraMap F k W.a₃)) * heq' +
      (Ψx * (L * x₁ * algebraMap F k W.a₁ * algebraMap F k W.a₃ * x +
        L * x₁ * algebraMap F k W.a₁ * x * y +
        L * x₁ * algebraMap F k W.a₃ * y -
        L * algebraMap F k W.a₁ * algebraMap F k W.a₃ * x ^ 2 -
        L * algebraMap F k W.a₁ * x ^ 2 * y -
        L * algebraMap F k W.a₃ * x * y -
        x₁ * algebraMap F k W.a₁ ^ 3 * x ^ 2 -
        x₁ * algebraMap F k W.a₁ * algebraMap F k W.a₂ * x ^ 2 -
        x₁ * algebraMap F k W.a₁ * algebraMap F k W.a₃ ^ 2 -
        x₁ * algebraMap F k W.a₁ * x ^ 3 -
        x₁ * algebraMap F k W.a₁ * y ^ 2 -
        x₁ * algebraMap F k W.a₂ * algebraMap F k W.a₃ * x -
        x₁ * algebraMap F k W.a₃ * algebraMap F k W.a₄ -
        2 * x₁ * algebraMap F k W.a₃ * x ^ 2 -
        algebraMap F k W.a₁ ^ 2 * algebraMap F k W.a₃ * x ^ 2 -
        algebraMap F k W.a₁ ^ 2 * x ^ 2 * y +
        algebraMap F k W.a₁ * algebraMap F k W.a₂ * x ^ 3 -
        algebraMap F k W.a₁ * algebraMap F k W.a₃ * x * y +
        algebraMap F k W.a₁ * x ^ 4 +
        algebraMap F k W.a₂ * algebraMap F k W.a₃ * x ^ 2 -
        algebraMap F k W.a₃ ^ 3 -
        algebraMap F k W.a₃ ^ 2 * y +
        algebraMap F k W.a₃ * algebraMap F k W.a₄ * x +
        2 * algebraMap F k W.a₃ * x ^ 3 -
        algebraMap F k W.a₃ * y ^ 2)) * h2 +
      (algebraMap F k W.a₁ * y ^ 2 +
        ((algebraMap F k W.a₃ + algebraMap F k W.a₁ ^ 3 + algebraMap F k W.a₁ * algebraMap F k W.a₂)
          * x ^ 2 +
        (algebraMap F k W.a₃ * algebraMap F k W.a₄ + algebraMap F k W.a₁ * algebraMap F k W.a₃ ^ 2 +
          algebraMap F k W.a₁ * algebraMap F k W.a₆))) * hxΦ

theorem main : ∃ (nX dX nY dY : F[X][Y]) (B : Set k), B.Finite ∧
    ∀ (x y : k) (h : (W.baseChange k).toAffine.Nonsingular x y), x ∉ B →
      evalEvalBC k dX (x ^ p) (y ^ p) ≠ 0 ∧ evalEvalBC k dY (x ^ p) (y ^ p) ≠ 0 ∧
      ∃ h', p • Affine.Point.some x y h = Affine.Point.some
        (evalEvalBC k nX (x ^ p) (y ^ p) / evalEvalBC k dX (x ^ p) (y ^ p))
        (evalEvalBC k nY (x ^ p) (y ^ p) / evalEvalBC k dY (x ^ p) (y ^ p)) h' := by
  by_cases hp2 : p = 2
  · exact main_two p k W hp2
  · exact main_odd p k W hp2

end Main

end WeierstrassCurve.VerschiebungSol
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_rational_verschiebung_of_charP.WeierstrassCurve P2MW.S_WeierstrassCurve_exists_rational_verschiebung_of_charP.WeierstrassCurve.VerschiebungSol"
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_rational_verschiebung_of_charP.WeierstrassCurve"

theorem solution {F : Type*} [Field F] (p : ℕ) [Fact p.Prime] [CharP F p] (k : Type*) [Field k] [Algebra F k] [IsAlgClosed k] [DecidableEq k] (W : WeierstrassCurve F) [W.IsElliptic] : ∃ (nX dX nY dY : Polynomial (Polynomial F)) (B : Set k), B.Finite ∧ ∀ (x y : k) (h : (W.baseChange k).toAffine.Nonsingular x y), x ∉ B → WeierstrassCurve.evalEvalBC k dX (x ^ p) (y ^ p) ≠ 0 ∧ WeierstrassCurve.evalEvalBC k dY (x ^ p) (y ^ p) ≠ 0 ∧ ∃ h', p • WeierstrassCurve.Affine.Point.some x y h = WeierstrassCurve.Affine.Point.some (WeierstrassCurve.evalEvalBC k nX (x ^ p) (y ^ p) / WeierstrassCurve.evalEvalBC k dX (x ^ p) (y ^ p)) (WeierstrassCurve.evalEvalBC k nY (x ^ p) (y ^ p) / WeierstrassCurve.evalEvalBC k dY (x ^ p) (y ^ p)) h' :=
  WeierstrassCurve.VerschiebungSol.main p k W

end S_WeierstrassCurve_exists_rational_verschiebung_of_charP
end P2MW
export P2MW.S_WeierstrassCurve_exists_rational_verschiebung_of_charP (solution)
