-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P12.clifford_three_cosets
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-22T02:04:13.59991+00:00
-- url     : https://prove2.me/submissions/f8a0056d-d041-4e11-9f40-407c0b289aaf

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P12

open QAlgorithms.Papers.Independent.Gap48.P12
noncomputable section


local notation "Mat" => Matrix Bool Bool ℂ

local notation "Vec" => EuclideanSpace ℂ Bool

local notation "wordMatrix" => fun (B : CircuitBasis) (w : CircuitWord) =>
  QAlgorithms.Papers.Independent.Next46.P21.wordMatrix (chronologicalInstructions B w)

namespace QAlgorithms.Papers.Independent
namespace ZW
open QAlgorithms Complex Gap48.P12

structure Z8 where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
  deriving DecidableEq

def Z8.add (x y : Z8) : Z8 := ⟨x.a + y.a, x.b + y.b, x.c + y.c, x.d + y.d⟩
def Z8.mul (x y : Z8) : Z8 :=
  ⟨x.a*y.a - x.b*y.d - x.c*y.c - x.d*y.b,
   x.a*y.b + x.b*y.a - x.c*y.d - x.d*y.c,
   x.a*y.c + x.b*y.b + x.c*y.a - x.d*y.d,
   x.a*y.d + x.b*y.c + x.c*y.b + x.d*y.a⟩
def z0 : Z8 := ⟨0, 0, 0, 0⟩
def z1 : Z8 := ⟨1, 0, 0, 0⟩
def rt2 : Z8 := ⟨0, 1, 0, -1⟩

structure E8 where
  p : Z8
  q : Z8
  r : Z8
  s : Z8
  deriving DecidableEq

def E8.mul (x y : E8) : E8 :=
  ⟨(x.p.mul y.p).add (x.q.mul y.r), (x.p.mul y.q).add (x.q.mul y.s),
   (x.r.mul y.p).add (x.s.mul y.r), (x.r.mul y.q).add (x.s.mul y.s)⟩
def E8.one : E8 := ⟨z1, z0, z0, z1⟩
def E8.sm (z : Z8) (e : E8) : E8 := ⟨z.mul e.p, z.mul e.q, z.mul e.r, z.mul e.s⟩
def E8.scale : ℕ → E8 → E8
  | 0, e => e
  | n + 1, e => E8.sm rt2 (E8.scale n e)

structure M8 where
  k : ℕ
  e : E8

def M8.mul (x y : M8) : M8 := ⟨x.k + y.k, x.e.mul y.e⟩
def M8.one : M8 := ⟨0, E8.one⟩

def Hn : E8 := ⟨z1, z1, z1, ⟨-1, 0, 0, 0⟩⟩
def Sn : E8 := ⟨z1, z0, z0, ⟨0, 0, 1, 0⟩⟩
def Tn : E8 := ⟨z1, z0, z0, ⟨0, 1, 0, 0⟩⟩
def Tdn : E8 := ⟨z1, z0, z0, ⟨0, 0, 0, -1⟩⟩
def H8 : M8 := ⟨1, Hn⟩
def S8 : M8 := ⟨0, Sn⟩
def T8 : M8 := ⟨0, Tn⟩
def Td8 : M8 := ⟨0, Tdn⟩

def g8 : CircuitLetter → M8
  | .h => H8
  | .p => S8
  | .t => T8

def ev8 (w : CircuitWord) : M8 := w.foldr (fun a m => (g8 a).mul m) M8.one

def keyN (n : ℕ) (x : M8) : E8 := E8.scale (n - x.k) x.e

/-! semantics -/
noncomputable def ω : ℂ := Complex.exp (Complex.I * Real.pi / 4)
noncomputable def sq : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)
noncomputable def cc : ℂ := sq⁻¹

noncomputable def φZ (z : Z8) : ℂ := z.a + z.b * ω + z.c * ω ^ 2 + z.d * ω ^ 3
noncomputable def φE (e : E8) : Matrix Bool Bool ℂ :=
  Matrix.of fun i j => match i, j with
    | false, false => φZ e.p
    | false, true => φZ e.q
    | true, false => φZ e.r
    | true, true => φZ e.s
noncomputable def φM (x : M8) : Matrix Bool Bool ℂ := cc ^ x.k • φE x.e

lemma sq_sq : sq ^ 2 = 2 := by
  unfold sq; rw [← ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
lemma sq_ne : sq ≠ 0 := by
  intro h; have := sq_sq; rw [h] at this; norm_num at this
lemma cc_sq : cc * sq = 1 := inv_mul_cancel₀ sq_ne

lemma ω_eq : ω = sq / 2 + sq / 2 * I := by
  unfold ω sq
  have : Complex.I * Real.pi / 4 = ((Real.pi / 4 : ℝ) : ℂ) * I := by push_cast; ring
  rw [this, Complex.exp_mul_I, ← ofReal_cos, ← ofReal_sin, Real.cos_pi_div_four,
    Real.sin_pi_div_four]
  push_cast; ring
lemma ω2 : ω ^ 2 = I := by
  rw [ω_eq]; linear_combination (sq ^ 2 / 4) * I_sq + (I / 2) * sq_sq
lemma ω3 : ω ^ 3 = sq / 2 * I - sq / 2 := by
  rw [pow_succ, ω2, ω_eq]; linear_combination (sq / 2) * I_sq
lemma ω4 : ω ^ 4 = -1 := by
  rw [show ω ^ 4 = (ω ^ 2) ^ 2 by ring, ω2, I_sq]

lemma φZ_add (x y : Z8) : φZ (x.add y) = φZ x + φZ y := by
  simp only [φZ, Z8.add]; push_cast; ring
lemma φZ_mul (x y : Z8) : φZ (x.mul y) = φZ x * φZ y := by
  simp only [φZ, Z8.mul]; push_cast
  linear_combination (-( ((x.b:ℂ)*y.d + x.c*y.c + x.d*y.b) + ((x.c:ℂ)*y.d + x.d*y.c) * ω +
    (x.d:ℂ)*y.d * ω^2)) * ω4
lemma φZ_rt2 : φZ rt2 = sq := by
  simp only [φZ, rt2]; push_cast; rw [ω3, ω2, ω_eq]; ring
lemma φZ_z0 : φZ z0 = 0 := by simp [φZ, z0]
lemma φZ_z1 : φZ z1 = 1 := by simp [φZ, z1]

lemma φE_mul (x y : E8) : φE (x.mul y) = φE x * φE y := by
  ext i j; cases i <;> cases j <;>
    simp [φE, E8.mul, Matrix.mul_apply, φZ_add, φZ_mul] <;> ring
lemma φE_sm (z : Z8) (e : E8) : φE (E8.sm z e) = φZ z • φE e := by
  ext i j; cases i <;> cases j <;> simp [φE, E8.sm, φZ_mul]
lemma φE_scale (n : ℕ) (e : E8) : φE (E8.scale n e) = sq ^ n • φE e := by
  induction n with
  | zero => simp [E8.scale]
  | succ n ih => rw [E8.scale, φE_sm, ih, φZ_rt2, smul_smul, pow_succ, mul_comm]
lemma φE_one : φE E8.one = 1 := by
  ext i j; cases i <;> cases j <;> simp [φE, E8.one, φZ_z0, φZ_z1]

lemma φM_mul (x y : M8) : φM (x.mul y) = φM x * φM y := by
  simp only [φM, M8.mul, φE_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, pow_add]
  rw [mul_comm (cc ^ y.k)]
lemma φM_one : φM M8.one = 1 := by simp [φM, M8.one, φE_one]

lemma key_spec (n : ℕ) (x : M8) (h : x.k ≤ n) : φM x = cc ^ n • φE (keyN n x) := by
  rw [keyN, φE_scale, smul_smul, φM]
  congr 1
  obtain ⟨m, rfl⟩ : ∃ m, n = x.k + m := ⟨n - x.k, by omega⟩
  rw [show x.k + m - x.k = m by omega, pow_add, mul_assoc, ← mul_pow, cc_sq, one_pow, mul_one]

lemma eq_of_key (n : ℕ) (x y : M8) (h : x.k ≤ n ∧ y.k ≤ n ∧ keyN n x = keyN n y) :
    φM x = φM y := by
  rw [key_spec n x h.1, key_spec n y h.2.1, h.2.2]

/-! injectivity -/
lemma lin_sqrt (u v : ℤ) (h : (u : ℝ) + Real.sqrt 2 * v = 0) : u = 0 ∧ v = 0 := by
  by_cases hv : v = 0
  · subst hv; simp at h; exact ⟨by exact_mod_cast h, rfl⟩
  · exfalso
    have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
    apply irrational_sqrt_two.ne_rat ((-u : ℚ) / v)
    push_cast; field_simp; linarith

lemma φZ_zero (a b c d : ℤ) (h : (a : ℂ) + b * ω + c * ω ^ 2 + d * ω ^ 3 = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  have e : (a : ℂ) + b * ω + c * ω ^ 2 + d * ω ^ 3 =
      (((2 * a : ℤ) : ℝ) + Real.sqrt 2 * ((b - d : ℤ) : ℝ) : ℝ) / 2 +
      ((((2 * c : ℤ) : ℝ) + Real.sqrt 2 * ((b + d : ℤ) : ℝ) : ℝ) : ℂ) / 2 * I := by
    rw [ω3, ω2, ω_eq]; unfold sq; push_cast; ring
  rw [e] at h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [Complex.add_re, Complex.add_im, Complex.div_ofNat_re, Complex.div_ofNat_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.zero_re, Complex.zero_im] at hre him
  have h1 := lin_sqrt _ _ (by linarith : (((2 * a : ℤ) : ℝ) + Real.sqrt 2 * ((b - d : ℤ) : ℝ)) = 0)
  have h2 := lin_sqrt _ _ (by linarith : (((2 * c : ℤ) : ℝ) + Real.sqrt 2 * ((b + d : ℤ) : ℝ)) = 0)
  omega

lemma φZ_inj (x y : Z8) (h : φZ x = φZ y) : x = y := by
  have := φZ_zero (x.a - y.a) (x.b - y.b) (x.c - y.c) (x.d - y.d) (by
    simp only [φZ] at h; push_cast; linear_combination h)
  obtain ⟨h1, h2, h3, h4⟩ := this
  cases x; cases y; simp only [Z8.mk.injEq] at *; omega

lemma φE_inj (x y : E8) (h : φE x = φE y) : x = y := by
  have e : ∀ i j, φE x i j = φE y i j := fun i j => by rw [h]
  have e1 := φZ_inj _ _ (e false false); have e2 := φZ_inj _ _ (e false true)
  have e3 := φZ_inj _ _ (e true false); have e4 := φZ_inj _ _ (e true true)
  cases x; cases y; simp_all [φE]

lemma ccpow_ne (n : ℕ) : cc ^ n ≠ 0 := pow_ne_zero _ (inv_ne_zero sq_ne)

lemma lvl_inj (n : ℕ) (e f : E8) (h : cc ^ n • φE e = cc ^ n • φE f) : e = f :=
  φE_inj _ _ (smul_right_injective _ (ccpow_ne n) h)

/-! generators -/
lemma φH : φM H8 = hadamard := by
  ext i j; cases i <;> cases j <;> simp [φM, H8, Hn, φE, φZ, hadamard, z1, cc, sq]
lemma φS : φM S8 = phaseS := by
  ext i j; cases i <;> cases j <;> simp [φM, S8, Sn, φE, φZ, phaseS, z1, z0, ω2]
lemma φT : φM T8 = gateT := by
  ext i j; cases i <;> cases j <;> simp [φM, T8, Tn, φE, φZ, gateT, z1, z0, ω]
lemma φTd : φM Td8 = star gateT := by
  have hc : (starRingEnd ℂ) ω = -ω ^ 3 := by
    rw [ω3, ω_eq]; unfold sq
    simp only [map_add, map_mul, map_div₀, Complex.conj_ofReal, Complex.conj_I, map_ofNat]; ring
  ext i j; cases i <;> cases j <;>
    simp [φM, Td8, Tdn, φE, φZ, gateT, z1, z0, Matrix.star_apply]
  rw [← hc]; rfl

lemma g8_spec (a : CircuitLetter) : φM (g8 a) = gateMatrix .hp a := by
  cases a
  · exact φH
  · exact φS
  · exact φT

def toL : CircuitLetter → Next46.P21.Letter
  | .h => .h
  | .p => .s
  | .t => .t

lemma chron (w : CircuitWord) : chronologicalInstructions .hp w = (w.map toL).reverse := by
  unfold chronologicalInstructions
  rw [← List.map_reverse]
  induction w.reverse with
  | nil => rfl
  | cons a L ih => cases a <;> simp [ih, toL]

lemma wm_eq (w : CircuitWord) :
    Next46.P21.wordMatrix (chronologicalInstructions .hp w) = φM (ev8 w) := by
  rw [chron, Next46.P21.wordMatrix, List.map_reverse, List.reverse_reverse]
  induction w with
  | nil => simp [ev8, φM_one]
  | cons a w ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [ih]
    show _ = φM ((g8 a).mul (ev8 w))
    rw [φM_mul, g8_spec]
    cases a <;> rfl

end ZW

namespace ZW
open QAlgorithms Gap48.P12
def KsLit : List E8 := [
  ⟨⟨0, 4, 0, -4⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 4, 0, -4⟩⟩,
  ⟨⟨0, 0, 0, 0⟩, ⟨-4, 0, -4, 0⟩, ⟨-4, 0, -4, 0⟩, ⟨0, 0, 0, 0⟩⟩,
  ⟨⟨0, 4, 0, -4⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 4, 0, 4⟩⟩,
  ⟨⟨0, 0, 0, 0⟩, ⟨0, -4, 0, -4⟩, ⟨0, -4, 0, -4⟩, ⟨0, 0, 0, 0⟩⟩,
  ⟨⟨0, 4, 0, -4⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, -4, 0, 4⟩⟩,
  ⟨⟨0, 0, 0, 0⟩, ⟨-4, 0, 4, 0⟩, ⟨4, 0, -4, 0⟩, ⟨0, 0, 0, 0⟩⟩,
  ⟨⟨0, 4, 0, -4⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, -4, 0, -4⟩⟩,
  ⟨⟨0, 4, 0, 4⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 4, 0, 4⟩⟩,
  ⟨⟨0, 0, 0, 0⟩, ⟨4, 0, -4, 0⟩, ⟨4, 0, 4, 0⟩, ⟨0, 0, 0, 0⟩⟩,
  ⟨⟨0, 0, 0, 0⟩, ⟨0, -4, 0, -4⟩, ⟨0, 4, 0, -4⟩, ⟨0, 0, 0, 0⟩⟩,
  ⟨⟨4, 0, 4, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨4, 0, -4, 0⟩⟩,
  ⟨⟨0, -4, 0, 4⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 4, 0, -4⟩⟩,
  ⟨⟨0, 0, 0, 0⟩, ⟨4, 0, 4, 0⟩, ⟨4, 0, 4, 0⟩, ⟨0, 0, 0, 0⟩⟩,
  ⟨⟨0, 0, 0, 0⟩, ⟨0, -4, 0, 4⟩, ⟨0, 4, 0, 4⟩, ⟨0, 0, 0, 0⟩⟩,
  ⟨⟨0, 0, 0, 0⟩, ⟨4, 0, -4, 0⟩, ⟨-4, 0, 4, 0⟩, ⟨0, 0, 0, 0⟩⟩,
  ⟨⟨4, 0, -4, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨-4, 0, 4, 0⟩⟩,
  ⟨⟨4, 0, 4, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨4, 0, 4, 0⟩⟩,
  ⟨⟨0, 0, 0, 0⟩, ⟨0, 4, 0, 4⟩, ⟨0, -4, 0, 4⟩, ⟨0, 0, 0, 0⟩⟩,
  ⟨⟨0, 0, 0, 0⟩, ⟨-4, 0, 4, 0⟩, ⟨4, 0, 4, 0⟩, ⟨0, 0, 0, 0⟩⟩,
  ⟨⟨0, 0, 0, 0⟩, ⟨0, 4, 0, -4⟩, ⟨0, -4, 0, -4⟩, ⟨0, 0, 0, 0⟩⟩,
  ⟨⟨0, 0, 0, 0⟩, ⟨4, 0, 4, 0⟩, ⟨-4, 0, 4, 0⟩, ⟨0, 0, 0, 0⟩⟩,
  ⟨⟨0, 0, 0, 0⟩, ⟨-4, 0, -4, 0⟩, ⟨4, 0, -4, 0⟩, ⟨0, 0, 0, 0⟩⟩,
  ⟨⟨0, 0, 0, 0⟩, ⟨4, 0, -4, 0⟩, ⟨-4, 0, -4, 0⟩, ⟨0, 0, 0, 0⟩⟩,
  ⟨⟨0, 4, 0, 4⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, -4, 0, 4⟩⟩,
  ⟨⟨4, 0, 4, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨-4, 0, 4, 0⟩⟩,
  ⟨⟨-4, 0, 4, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨-4, 0, -4, 0⟩⟩,
  ⟨⟨0, 0, 0, 0⟩, ⟨0, 4, 0, -4⟩, ⟨0, 4, 0, -4⟩, ⟨0, 0, 0, 0⟩⟩,
  ⟨⟨0, -4, 0, 4⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 4, 0, 4⟩⟩,
  ⟨⟨0, 0, 0, 0⟩, ⟨-4, 0, -4, 0⟩, ⟨4, 0, 4, 0⟩, ⟨0, 0, 0, 0⟩⟩,
  ⟨⟨0, -4, 0, -4⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 4, 0, -4⟩⟩,
  ⟨⟨0, 0, 0, 0⟩, ⟨0, -4, 0, -4⟩, ⟨0, 4, 0, 4⟩, ⟨0, 0, 0, 0⟩⟩,
  ⟨⟨4, 0, -4, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨-4, 0, -4, 0⟩⟩,
  ⟨⟨0, 0, 0, 0⟩, ⟨-4, 0, 4, 0⟩, ⟨-4, 0, 4, 0⟩, ⟨0, 0, 0, 0⟩⟩,
  ⟨⟨0, 0, 0, 0⟩, ⟨0, -4, 0, 4⟩, ⟨0, -4, 0, 4⟩, ⟨0, 0, 0, 0⟩⟩,
  ⟨⟨0, 0, 0, 0⟩, ⟨4, 0, 4, 0⟩, ⟨-4, 0, -4, 0⟩, ⟨0, 0, 0, 0⟩⟩,
  ⟨⟨0, 0, 0, 0⟩, ⟨0, 4, 0, 4⟩, ⟨0, -4, 0, -4⟩, ⟨0, 0, 0, 0⟩⟩,
  ⟨⟨0, 0, 0, 0⟩, ⟨4, 0, -4, 0⟩, ⟨4, 0, -4, 0⟩, ⟨0, 0, 0, 0⟩⟩,
  ⟨⟨-4, 0, 4, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨4, 0, -4, 0⟩⟩,
  ⟨⟨4, 0, 4, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨-4, 0, -4, 0⟩⟩,
  ⟨⟨0, -4, 0, 4⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, -4, 0, 4⟩⟩,
  ⟨⟨0, 4, 0, 4⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, -4, 0, -4⟩⟩,
  ⟨⟨0, -4, 0, -4⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 4, 0, 4⟩⟩,
  ⟨⟨0, 0, 0, 0⟩, ⟨0, 4, 0, 4⟩, ⟨0, 4, 0, -4⟩, ⟨0, 0, 0, 0⟩⟩,
  ⟨⟨4, 0, -4, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨4, 0, -4, 0⟩⟩,
  ⟨⟨0, 0, 0, 0⟩, ⟨0, 4, 0, -4⟩, ⟨0, 4, 0, 4⟩, ⟨0, 0, 0, 0⟩⟩,
  ⟨⟨0, 0, 0, 0⟩, ⟨0, -4, 0, 4⟩, ⟨0, -4, 0, -4⟩, ⟨0, 0, 0, 0⟩⟩,
  ⟨⟨0, 0, 0, 0⟩, ⟨-4, 0, -4, 0⟩, ⟨-4, 0, 4, 0⟩, ⟨0, 0, 0, 0⟩⟩,
  ⟨⟨-4, 0, 4, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨4, 0, 4, 0⟩⟩,
  ⟨⟨0, 0, 0, 0⟩, ⟨0, -4, 0, -4⟩, ⟨0, -4, 0, 4⟩, ⟨0, 0, 0, 0⟩⟩,
  ⟨⟨-4, 0, -4, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨4, 0, -4, 0⟩⟩,
  ⟨⟨0, 0, 0, 0⟩, ⟨-4, 0, 4, 0⟩, ⟨-4, 0, -4, 0⟩, ⟨0, 0, 0, 0⟩⟩,
  ⟨⟨0, -4, 0, 4⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, -4, 0, -4⟩⟩,
  ⟨⟨0, 0, 0, 0⟩, ⟨4, 0, 4, 0⟩, ⟨4, 0, -4, 0⟩, ⟨0, 0, 0, 0⟩⟩,
  ⟨⟨0, -4, 0, -4⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, -4, 0, 4⟩⟩,
  ⟨⟨0, 4, 0, 4⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 4, 0, -4⟩⟩,
  ⟨⟨-4, 0, 4, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨-4, 0, 4, 0⟩⟩,
  ⟨⟨0, 0, 0, 0⟩, ⟨0, -4, 0, 4⟩, ⟨0, 4, 0, -4⟩, ⟨0, 0, 0, 0⟩⟩,
  ⟨⟨-4, 0, -4, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨4, 0, 4, 0⟩⟩,
  ⟨⟨0, 0, 0, 0⟩, ⟨0, 4, 0, 4⟩, ⟨0, 4, 0, 4⟩, ⟨0, 0, 0, 0⟩⟩,
  ⟨⟨0, -4, 0, -4⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, -4, 0, -4⟩⟩,
  ⟨⟨4, 0, -4, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨4, 0, 4, 0⟩⟩,
  ⟨⟨-4, 0, -4, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨-4, 0, 4, 0⟩⟩,
  ⟨⟨0, 0, 0, 0⟩, ⟨0, 4, 0, -4⟩, ⟨0, -4, 0, 4⟩, ⟨0, 0, 0, 0⟩⟩,
  ⟨⟨-4, 0, -4, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨-4, 0, -4, 0⟩⟩,
  ⟨⟨4, 0, 0, 0⟩, ⟨4, 0, 0, 0⟩, ⟨4, 0, 0, 0⟩, ⟨-4, 0, 0, 0⟩⟩,
  ⟨⟨0, -4, 0, 0⟩, ⟨0, -4, 0, 0⟩, ⟨0, 4, 0, 0⟩, ⟨0, -4, 0, 0⟩⟩,
  ⟨⟨4, 0, 0, 0⟩, ⟨0, 0, 4, 0⟩, ⟨4, 0, 0, 0⟩, ⟨0, 0, -4, 0⟩⟩,
  ⟨⟨0, 0, -4, 0⟩, ⟨0, 0, -4, 0⟩, ⟨0, 0, 4, 0⟩, ⟨0, 0, -4, 0⟩⟩,
  ⟨⟨4, 0, 0, 0⟩, ⟨-4, 0, 0, 0⟩, ⟨4, 0, 0, 0⟩, ⟨4, 0, 0, 0⟩⟩,
  ⟨⟨0, 0, 0, -4⟩, ⟨0, 0, 0, 4⟩, ⟨0, 0, 0, 4⟩, ⟨0, 0, 0, 4⟩⟩,
  ⟨⟨4, 0, 0, 0⟩, ⟨0, 0, -4, 0⟩, ⟨4, 0, 0, 0⟩, ⟨0, 0, 4, 0⟩⟩,
  ⟨⟨0, 0, 4, 0⟩, ⟨0, 0, 4, 0⟩, ⟨0, 0, 4, 0⟩, ⟨0, 0, -4, 0⟩⟩,
  ⟨⟨0, 4, 0, 0⟩, ⟨0, 0, 0, -4⟩, ⟨0, -4, 0, 0⟩, ⟨0, 0, 0, -4⟩⟩,
  ⟨⟨4, 0, 0, 0⟩, ⟨0, 0, -4, 0⟩, ⟨-4, 0, 0, 0⟩, ⟨0, 0, -4, 0⟩⟩,
  ⟨⟨0, 4, 0, 0⟩, ⟨0, 0, 0, -4⟩, ⟨0, 4, 0, 0⟩, ⟨0, 0, 0, 4⟩⟩,
  ⟨⟨-4, 0, 0, 0⟩, ⟨4, 0, 0, 0⟩, ⟨-4, 0, 0, 0⟩, ⟨-4, 0, 0, 0⟩⟩,
  ⟨⟨0, 4, 0, 0⟩, ⟨0, 4, 0, 0⟩, ⟨0, -4, 0, 0⟩, ⟨0, 4, 0, 0⟩⟩,
  ⟨⟨0, 0, 4, 0⟩, ⟨-4, 0, 0, 0⟩, ⟨0, 0, -4, 0⟩, ⟨-4, 0, 0, 0⟩⟩,
  ⟨⟨0, 0, 0, 4⟩, ⟨0, 0, 0, -4⟩, ⟨0, 0, 0, -4⟩, ⟨0, 0, 0, -4⟩⟩,
  ⟨⟨0, 0, 0, -4⟩, ⟨0, 0, 0, 4⟩, ⟨0, 0, 0, -4⟩, ⟨0, 0, 0, -4⟩⟩,
  ⟨⟨0, 4, 0, 0⟩, ⟨0, 4, 0, 0⟩, ⟨0, 4, 0, 0⟩, ⟨0, -4, 0, 0⟩⟩,
  ⟨⟨-4, 0, 0, 0⟩, ⟨0, 0, 4, 0⟩, ⟨4, 0, 0, 0⟩, ⟨0, 0, 4, 0⟩⟩,
  ⟨⟨0, 4, 0, 0⟩, ⟨0, 0, 0, 4⟩, ⟨0, -4, 0, 0⟩, ⟨0, 0, 0, 4⟩⟩,
  ⟨⟨0, 0, -4, 0⟩, ⟨4, 0, 0, 0⟩, ⟨0, 0, 4, 0⟩, ⟨4, 0, 0, 0⟩⟩,
  ⟨⟨0, 0, 0, 4⟩, ⟨0, 4, 0, 0⟩, ⟨0, 0, 0, -4⟩, ⟨0, 4, 0, 0⟩⟩,
  ⟨⟨0, 0, 0, -4⟩, ⟨0, -4, 0, 0⟩, ⟨0, 0, 0, 4⟩, ⟨0, -4, 0, 0⟩⟩,
  ⟨⟨0, -4, 0, 0⟩, ⟨0, 0, 0, -4⟩, ⟨0, 4, 0, 0⟩, ⟨0, 0, 0, -4⟩⟩,
  ⟨⟨0, 0, 4, 0⟩, ⟨-4, 0, 0, 0⟩, ⟨0, 0, 4, 0⟩, ⟨4, 0, 0, 0⟩⟩,
  ⟨⟨0, 4, 0, 0⟩, ⟨0, 0, 0, 4⟩, ⟨0, 4, 0, 0⟩, ⟨0, 0, 0, -4⟩⟩,
  ⟨⟨0, 0, 0, 4⟩, ⟨0, -4, 0, 0⟩, ⟨0, 0, 0, 4⟩, ⟨0, 4, 0, 0⟩⟩,
  ⟨⟨4, 0, 0, 0⟩, ⟨4, 0, 0, 0⟩, ⟨-4, 0, 0, 0⟩, ⟨4, 0, 0, 0⟩⟩,
  ⟨⟨-4, 0, 0, 0⟩, ⟨0, 0, 4, 0⟩, ⟨-4, 0, 0, 0⟩, ⟨0, 0, -4, 0⟩⟩,
  ⟨⟨0, 4, 0, 0⟩, ⟨0, -4, 0, 0⟩, ⟨0, -4, 0, 0⟩, ⟨0, -4, 0, 0⟩⟩,
  ⟨⟨0, 0, -4, 0⟩, ⟨4, 0, 0, 0⟩, ⟨0, 0, -4, 0⟩, ⟨-4, 0, 0, 0⟩⟩,
  ⟨⟨0, 0, 4, 0⟩, ⟨0, 0, -4, 0⟩, ⟨0, 0, -4, 0⟩, ⟨0, 0, -4, 0⟩⟩,
  ⟨⟨0, 0, 0, -4⟩, ⟨0, -4, 0, 0⟩, ⟨0, 0, 0, -4⟩, ⟨0, 4, 0, 0⟩⟩,
  ⟨⟨0, 0, 0, 4⟩, ⟨0, 0, 0, 4⟩, ⟨0, 0, 0, -4⟩, ⟨0, 0, 0, 4⟩⟩,
  ⟨⟨-4, 0, 0, 0⟩, ⟨-4, 0, 0, 0⟩, ⟨4, 0, 0, 0⟩, ⟨-4, 0, 0, 0⟩⟩,
  ⟨⟨0, -4, 0, 0⟩, ⟨0, 4, 0, 0⟩, ⟨0, 4, 0, 0⟩, ⟨0, 4, 0, 0⟩⟩,
  ⟨⟨0, 0, -4, 0⟩, ⟨0, 0, 4, 0⟩, ⟨0, 0, 4, 0⟩, ⟨0, 0, 4, 0⟩⟩,
  ⟨⟨0, 0, 0, -4⟩, ⟨0, 0, 0, -4⟩, ⟨0, 0, 0, 4⟩, ⟨0, 0, 0, -4⟩⟩,
  ⟨⟨0, 0, 0, 4⟩, ⟨0, 0, 0, -4⟩, ⟨0, 0, 0, 4⟩, ⟨0, 0, 0, 4⟩⟩,
  ⟨⟨0, 4, 0, 0⟩, ⟨0, -4, 0, 0⟩, ⟨0, 4, 0, 0⟩, ⟨0, 4, 0, 0⟩⟩,
  ⟨⟨-4, 0, 0, 0⟩, ⟨-4, 0, 0, 0⟩, ⟨-4, 0, 0, 0⟩, ⟨4, 0, 0, 0⟩⟩,
  ⟨⟨0, 0, 4, 0⟩, ⟨0, 0, -4, 0⟩, ⟨0, 0, 4, 0⟩, ⟨0, 0, 4, 0⟩⟩,
  ⟨⟨0, 0, -4, 0⟩, ⟨0, 0, 4, 0⟩, ⟨0, 0, -4, 0⟩, ⟨0, 0, -4, 0⟩⟩,
  ⟨⟨4, 0, 0, 0⟩, ⟨0, 0, 4, 0⟩, ⟨-4, 0, 0, 0⟩, ⟨0, 0, 4, 0⟩⟩,
  ⟨⟨0, 0, 0, -4⟩, ⟨0, 0, 0, -4⟩, ⟨0, 0, 0, -4⟩, ⟨0, 0, 0, 4⟩⟩,
  ⟨⟨0, 0, 4, 0⟩, ⟨4, 0, 0, 0⟩, ⟨0, 0, -4, 0⟩, ⟨4, 0, 0, 0⟩⟩,
  ⟨⟨0, 0, -4, 0⟩, ⟨-4, 0, 0, 0⟩, ⟨0, 0, 4, 0⟩, ⟨-4, 0, 0, 0⟩⟩,
  ⟨⟨0, 0, 0, 4⟩, ⟨0, -4, 0, 0⟩, ⟨0, 0, 0, -4⟩, ⟨0, -4, 0, 0⟩⟩,
  ⟨⟨0, 0, 0, 4⟩, ⟨0, 4, 0, 0⟩, ⟨0, 0, 0, 4⟩, ⟨0, -4, 0, 0⟩⟩,
  ⟨⟨-4, 0, 0, 0⟩, ⟨0, 0, -4, 0⟩, ⟨4, 0, 0, 0⟩, ⟨0, 0, -4, 0⟩⟩,
  ⟨⟨0, -4, 0, 0⟩, ⟨0, 0, 0, -4⟩, ⟨0, -4, 0, 0⟩, ⟨0, 0, 0, 4⟩⟩,
  ⟨⟨0, -4, 0, 0⟩, ⟨0, 0, 0, 4⟩, ⟨0, 4, 0, 0⟩, ⟨0, 0, 0, 4⟩⟩,
  ⟨⟨-4, 0, 0, 0⟩, ⟨0, 0, -4, 0⟩, ⟨-4, 0, 0, 0⟩, ⟨0, 0, 4, 0⟩⟩,
  ⟨⟨0, 0, 0, -4⟩, ⟨0, 4, 0, 0⟩, ⟨0, 0, 0, 4⟩, ⟨0, 4, 0, 0⟩⟩,
  ⟨⟨0, 0, -4, 0⟩, ⟨-4, 0, 0, 0⟩, ⟨0, 0, -4, 0⟩, ⟨4, 0, 0, 0⟩⟩,
  ⟨⟨0, 0, 4, 0⟩, ⟨4, 0, 0, 0⟩, ⟨0, 0, 4, 0⟩, ⟨-4, 0, 0, 0⟩⟩,
  ⟨⟨0, 0, 0, 4⟩, ⟨0, 0, 0, 4⟩, ⟨0, 0, 0, 4⟩, ⟨0, 0, 0, -4⟩⟩,
  ⟨⟨4, 0, 0, 0⟩, ⟨-4, 0, 0, 0⟩, ⟨-4, 0, 0, 0⟩, ⟨-4, 0, 0, 0⟩⟩,
  ⟨⟨0, -4, 0, 0⟩, ⟨0, 4, 0, 0⟩, ⟨0, -4, 0, 0⟩, ⟨0, -4, 0, 0⟩⟩,
  ⟨⟨0, 0, 4, 0⟩, ⟨0, 0, 4, 0⟩, ⟨0, 0, -4, 0⟩, ⟨0, 0, 4, 0⟩⟩,
  ⟨⟨0, 0, -4, 0⟩, ⟨0, 0, -4, 0⟩, ⟨0, 0, -4, 0⟩, ⟨0, 0, 4, 0⟩⟩,
  ⟨⟨0, 0, 0, -4⟩, ⟨0, 4, 0, 0⟩, ⟨0, 0, 0, -4⟩, ⟨0, -4, 0, 0⟩⟩,
  ⟨⟨0, -4, 0, 0⟩, ⟨0, 0, 0, 4⟩, ⟨0, -4, 0, 0⟩, ⟨0, 0, 0, -4⟩⟩,
  ⟨⟨-4, 0, 0, 0⟩, ⟨4, 0, 0, 0⟩, ⟨4, 0, 0, 0⟩, ⟨4, 0, 0, 0⟩⟩,
  ⟨⟨0, -4, 0, 0⟩, ⟨0, -4, 0, 0⟩, ⟨0, -4, 0, 0⟩, ⟨0, 4, 0, 0⟩⟩,
  ⟨⟨4, 0, 0, 0⟩, ⟨4, 0, 0, 0⟩, ⟨0, 0, 4, 0⟩, ⟨0, 0, -4, 0⟩⟩,
  ⟨⟨0, -4, 0, 0⟩, ⟨0, -4, 0, 0⟩, ⟨0, 0, 0, 4⟩, ⟨0, 0, 0, -4⟩⟩,
  ⟨⟨4, 0, 0, 0⟩, ⟨0, 0, 4, 0⟩, ⟨0, 0, 4, 0⟩, ⟨4, 0, 0, 0⟩⟩,
  ⟨⟨0, 0, -4, 0⟩, ⟨0, 0, -4, 0⟩, ⟨-4, 0, 0, 0⟩, ⟨4, 0, 0, 0⟩⟩,
  ⟨⟨4, 0, 0, 0⟩, ⟨-4, 0, 0, 0⟩, ⟨0, 0, 4, 0⟩, ⟨0, 0, 4, 0⟩⟩,
  ⟨⟨0, 0, 0, -4⟩, ⟨0, 0, 0, 4⟩, ⟨0, -4, 0, 0⟩, ⟨0, -4, 0, 0⟩⟩,
  ⟨⟨4, 0, 0, 0⟩, ⟨0, 0, -4, 0⟩, ⟨0, 0, 4, 0⟩, ⟨-4, 0, 0, 0⟩⟩,
  ⟨⟨0, 0, 4, 0⟩, ⟨0, 0, 4, 0⟩, ⟨-4, 0, 0, 0⟩, ⟨4, 0, 0, 0⟩⟩,
  ⟨⟨0, 4, 0, 0⟩, ⟨0, 0, 0, -4⟩, ⟨0, 0, 0, -4⟩, ⟨0, 4, 0, 0⟩⟩,
  ⟨⟨4, 0, 0, 0⟩, ⟨0, 0, -4, 0⟩, ⟨0, 0, -4, 0⟩, ⟨4, 0, 0, 0⟩⟩,
  ⟨⟨0, 4, 0, 0⟩, ⟨0, 0, 0, -4⟩, ⟨0, 0, 0, 4⟩, ⟨0, -4, 0, 0⟩⟩,
  ⟨⟨-4, 0, 0, 0⟩, ⟨4, 0, 0, 0⟩, ⟨0, 0, -4, 0⟩, ⟨0, 0, -4, 0⟩⟩,
  ⟨⟨0, 4, 0, 0⟩, ⟨0, 4, 0, 0⟩, ⟨0, 0, 0, -4⟩, ⟨0, 0, 0, 4⟩⟩,
  ⟨⟨0, 0, 4, 0⟩, ⟨-4, 0, 0, 0⟩, ⟨4, 0, 0, 0⟩, ⟨0, 0, -4, 0⟩⟩,
  ⟨⟨0, 0, 0, 4⟩, ⟨0, 0, 0, -4⟩, ⟨0, 4, 0, 0⟩, ⟨0, 4, 0, 0⟩⟩,
  ⟨⟨0, 0, 0, -4⟩, ⟨0, 0, 0, 4⟩, ⟨0, 4, 0, 0⟩, ⟨0, 4, 0, 0⟩⟩,
  ⟨⟨0, 4, 0, 0⟩, ⟨0, 4, 0, 0⟩, ⟨0, 0, 0, 4⟩, ⟨0, 0, 0, -4⟩⟩,
  ⟨⟨-4, 0, 0, 0⟩, ⟨0, 0, 4, 0⟩, ⟨0, 0, 4, 0⟩, ⟨-4, 0, 0, 0⟩⟩,
  ⟨⟨0, 4, 0, 0⟩, ⟨0, 0, 0, 4⟩, ⟨0, 0, 0, -4⟩, ⟨0, -4, 0, 0⟩⟩,
  ⟨⟨0, 0, -4, 0⟩, ⟨4, 0, 0, 0⟩, ⟨-4, 0, 0, 0⟩, ⟨0, 0, 4, 0⟩⟩,
  ⟨⟨0, 0, 0, 4⟩, ⟨0, 4, 0, 0⟩, ⟨0, 4, 0, 0⟩, ⟨0, 0, 0, 4⟩⟩,
  ⟨⟨0, 0, 0, -4⟩, ⟨0, -4, 0, 0⟩, ⟨0, -4, 0, 0⟩, ⟨0, 0, 0, -4⟩⟩,
  ⟨⟨0, -4, 0, 0⟩, ⟨0, 0, 0, -4⟩, ⟨0, 0, 0, 4⟩, ⟨0, 4, 0, 0⟩⟩,
  ⟨⟨0, 0, 4, 0⟩, ⟨-4, 0, 0, 0⟩, ⟨-4, 0, 0, 0⟩, ⟨0, 0, 4, 0⟩⟩,
  ⟨⟨0, 4, 0, 0⟩, ⟨0, 0, 0, 4⟩, ⟨0, 0, 0, 4⟩, ⟨0, 4, 0, 0⟩⟩,
  ⟨⟨0, 0, 0, 4⟩, ⟨0, -4, 0, 0⟩, ⟨0, -4, 0, 0⟩, ⟨0, 0, 0, 4⟩⟩,
  ⟨⟨4, 0, 0, 0⟩, ⟨4, 0, 0, 0⟩, ⟨0, 0, -4, 0⟩, ⟨0, 0, 4, 0⟩⟩,
  ⟨⟨-4, 0, 0, 0⟩, ⟨0, 0, 4, 0⟩, ⟨0, 0, -4, 0⟩, ⟨4, 0, 0, 0⟩⟩,
  ⟨⟨0, 4, 0, 0⟩, ⟨0, -4, 0, 0⟩, ⟨0, 0, 0, -4⟩, ⟨0, 0, 0, -4⟩⟩,
  ⟨⟨0, 0, -4, 0⟩, ⟨4, 0, 0, 0⟩, ⟨4, 0, 0, 0⟩, ⟨0, 0, -4, 0⟩⟩,
  ⟨⟨0, 0, 4, 0⟩, ⟨0, 0, -4, 0⟩, ⟨4, 0, 0, 0⟩, ⟨4, 0, 0, 0⟩⟩,
  ⟨⟨0, 0, 0, -4⟩, ⟨0, -4, 0, 0⟩, ⟨0, 4, 0, 0⟩, ⟨0, 0, 0, 4⟩⟩,
  ⟨⟨0, 0, 0, 4⟩, ⟨0, 0, 0, 4⟩, ⟨0, 4, 0, 0⟩, ⟨0, -4, 0, 0⟩⟩,
  ⟨⟨-4, 0, 0, 0⟩, ⟨-4, 0, 0, 0⟩, ⟨0, 0, 4, 0⟩, ⟨0, 0, -4, 0⟩⟩,
  ⟨⟨0, -4, 0, 0⟩, ⟨0, 4, 0, 0⟩, ⟨0, 0, 0, 4⟩, ⟨0, 0, 0, 4⟩⟩,
  ⟨⟨0, 0, -4, 0⟩, ⟨0, 0, 4, 0⟩, ⟨-4, 0, 0, 0⟩, ⟨-4, 0, 0, 0⟩⟩,
  ⟨⟨0, 0, 0, -4⟩, ⟨0, 0, 0, -4⟩, ⟨0, -4, 0, 0⟩, ⟨0, 4, 0, 0⟩⟩,
  ⟨⟨0, 0, 0, 4⟩, ⟨0, 0, 0, -4⟩, ⟨0, -4, 0, 0⟩, ⟨0, -4, 0, 0⟩⟩,
  ⟨⟨0, 4, 0, 0⟩, ⟨0, -4, 0, 0⟩, ⟨0, 0, 0, 4⟩, ⟨0, 0, 0, 4⟩⟩,
  ⟨⟨-4, 0, 0, 0⟩, ⟨-4, 0, 0, 0⟩, ⟨0, 0, -4, 0⟩, ⟨0, 0, 4, 0⟩⟩,
  ⟨⟨0, 0, 4, 0⟩, ⟨0, 0, -4, 0⟩, ⟨-4, 0, 0, 0⟩, ⟨-4, 0, 0, 0⟩⟩,
  ⟨⟨0, 0, -4, 0⟩, ⟨0, 0, 4, 0⟩, ⟨4, 0, 0, 0⟩, ⟨4, 0, 0, 0⟩⟩,
  ⟨⟨4, 0, 0, 0⟩, ⟨0, 0, 4, 0⟩, ⟨0, 0, -4, 0⟩, ⟨-4, 0, 0, 0⟩⟩,
  ⟨⟨0, 0, 0, -4⟩, ⟨0, 0, 0, -4⟩, ⟨0, 4, 0, 0⟩, ⟨0, -4, 0, 0⟩⟩,
  ⟨⟨0, 0, 4, 0⟩, ⟨4, 0, 0, 0⟩, ⟨4, 0, 0, 0⟩, ⟨0, 0, 4, 0⟩⟩,
  ⟨⟨0, 0, -4, 0⟩, ⟨-4, 0, 0, 0⟩, ⟨-4, 0, 0, 0⟩, ⟨0, 0, -4, 0⟩⟩,
  ⟨⟨0, 0, 0, 4⟩, ⟨0, -4, 0, 0⟩, ⟨0, 4, 0, 0⟩, ⟨0, 0, 0, -4⟩⟩,
  ⟨⟨0, 0, 0, 4⟩, ⟨0, 4, 0, 0⟩, ⟨0, -4, 0, 0⟩, ⟨0, 0, 0, -4⟩⟩,
  ⟨⟨-4, 0, 0, 0⟩, ⟨0, 0, -4, 0⟩, ⟨0, 0, 4, 0⟩, ⟨4, 0, 0, 0⟩⟩,
  ⟨⟨0, -4, 0, 0⟩, ⟨0, 0, 0, -4⟩, ⟨0, 0, 0, -4⟩, ⟨0, -4, 0, 0⟩⟩,
  ⟨⟨0, -4, 0, 0⟩, ⟨0, 0, 0, 4⟩, ⟨0, 0, 0, 4⟩, ⟨0, -4, 0, 0⟩⟩,
  ⟨⟨-4, 0, 0, 0⟩, ⟨0, 0, -4, 0⟩, ⟨0, 0, -4, 0⟩, ⟨-4, 0, 0, 0⟩⟩,
  ⟨⟨0, 0, 0, -4⟩, ⟨0, 4, 0, 0⟩, ⟨0, -4, 0, 0⟩, ⟨0, 0, 0, 4⟩⟩,
  ⟨⟨0, 0, -4, 0⟩, ⟨-4, 0, 0, 0⟩, ⟨4, 0, 0, 0⟩, ⟨0, 0, 4, 0⟩⟩,
  ⟨⟨0, 0, 4, 0⟩, ⟨4, 0, 0, 0⟩, ⟨-4, 0, 0, 0⟩, ⟨0, 0, -4, 0⟩⟩,
  ⟨⟨0, 0, 0, 4⟩, ⟨0, 0, 0, 4⟩, ⟨0, -4, 0, 0⟩, ⟨0, 4, 0, 0⟩⟩,
  ⟨⟨4, 0, 0, 0⟩, ⟨-4, 0, 0, 0⟩, ⟨0, 0, -4, 0⟩, ⟨0, 0, -4, 0⟩⟩,
  ⟨⟨0, -4, 0, 0⟩, ⟨0, 4, 0, 0⟩, ⟨0, 0, 0, -4⟩, ⟨0, 0, 0, -4⟩⟩,
  ⟨⟨0, 0, 4, 0⟩, ⟨0, 0, 4, 0⟩, ⟨4, 0, 0, 0⟩, ⟨-4, 0, 0, 0⟩⟩,
  ⟨⟨0, 0, -4, 0⟩, ⟨0, 0, -4, 0⟩, ⟨4, 0, 0, 0⟩, ⟨-4, 0, 0, 0⟩⟩,
  ⟨⟨0, 0, 0, -4⟩, ⟨0, 4, 0, 0⟩, ⟨0, 4, 0, 0⟩, ⟨0, 0, 0, -4⟩⟩,
  ⟨⟨0, -4, 0, 0⟩, ⟨0, 0, 0, 4⟩, ⟨0, 0, 0, -4⟩, ⟨0, 4, 0, 0⟩⟩,
  ⟨⟨-4, 0, 0, 0⟩, ⟨4, 0, 0, 0⟩, ⟨0, 0, 4, 0⟩, ⟨0, 0, 4, 0⟩⟩,
  ⟨⟨0, -4, 0, 0⟩, ⟨0, -4, 0, 0⟩, ⟨0, 0, 0, -4⟩, ⟨0, 0, 0, 4⟩⟩]

def Ks : List E8 := rewriteTable.map (fun row => keyN 5 (ev8 row.1))

set_option maxRecDepth 100000
lemma c_Ks : Ks = KsLit := by decide +kernel
lemma c_k : ∀ row ∈ rewriteTable, (ev8 row.1).k ≤ 5 := by decide +kernel
lemma c_t : ∀ row ∈ rewriteTable, CircuitLetter.t ∉ row.1 := by decide +kernel
lemma c_H : ∀ e ∈ KsLit, ∃ f ∈ KsLit, Hn.mul e = E8.sm rt2 f := by decide +kernel
lemma c_S : ∀ e ∈ KsLit, Sn.mul e ∈ KsLit := by decide +kernel
lemma c_1 : E8.scale 5 E8.one ∈ KsLit := by decide +kernel
lemma Ks_mem (e : E8) (he : e ∈ KsLit) : ∃ row ∈ rewriteTable, keyN 5 (ev8 row.1) = e := by
  rw [← c_Ks, Ks, List.mem_map] at he; exact he

noncomputable def InK (U : Matrix Bool Bool ℂ) : Prop := ∃ e ∈ KsLit, U = cc ^ 5 • φE e

lemma InK_one : InK 1 := ⟨_, c_1, by
  rw [φE_scale, φE_one, smul_smul, ← mul_pow, cc_sq, one_pow, one_smul]⟩

lemma InK_H (U) (h : InK U) : InK (hadamard * U) := by
  obtain ⟨e, he, rfl⟩ := h
  obtain ⟨f, hf, hfe⟩ := c_H e he
  refine ⟨f, hf, ?_⟩
  rw [← φH, φM, H8, Matrix.smul_mul, Matrix.mul_smul, ← φE_mul, hfe, φE_sm, φZ_rt2, smul_smul,
    smul_smul]
  congr 1
  linear_combination (cc ^ 5) * cc_sq

lemma InK_S (U) (h : InK U) : InK (phaseS * U) := by
  obtain ⟨e, he, rfl⟩ := h
  refine ⟨_, c_S e he, ?_⟩
  rw [← φS, φM, S8, Matrix.smul_mul, Matrix.mul_smul, ← φE_mul, pow_zero, one_smul]

lemma InK_word (w : CircuitWord) (hw : CircuitLetter.t ∉ w) :
    InK (φM (ev8 w)) := by
  induction w with
  | nil => simpa [ev8, φM_one] using InK_one
  | cons a w ih =>
    have hw' : CircuitLetter.t ∉ w := fun h => hw (List.mem_cons_of_mem _ h)
    show InK (φM ((g8 a).mul (ev8 w)))
    rw [φM_mul, g8_spec]
    cases a
    · exact InK_H _ (ih hw')
    · exact InK_S _ (ih hw')
    · exact absurd List.mem_cons_self hw



def CTLit : List E8 := [
  ⟨⟨0, 4, 0, -4⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 4, 0, -4⟩⟩,
  ⟨⟨0, 0, 0, 0⟩, ⟨0, -4, 0, 4⟩, ⟨0, -4, 0, -4⟩, ⟨0, 0, 0, 0⟩⟩,
  ⟨⟨0, 4, 0, -4⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 4, 0, 4⟩⟩,
  ⟨⟨0, 0, 0, 0⟩, ⟨-4, 0, -4, 0⟩, ⟨4, 0, -4, 0⟩, ⟨0, 0, 0, 0⟩⟩,
  ⟨⟨0, 4, 0, -4⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, -4, 0, 4⟩⟩,
  ⟨⟨0, 0, 0, 0⟩, ⟨0, 4, 0, 4⟩, ⟨0, 4, 0, -4⟩, ⟨0, 0, 0, 0⟩⟩,
  ⟨⟨0, 4, 0, -4⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, -4, 0, -4⟩⟩,
  ⟨⟨0, 4, 0, 4⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 4, 0, 4⟩⟩,
  ⟨⟨0, 0, 0, 0⟩, ⟨0, -4, 0, -4⟩, ⟨0, 4, 0, 4⟩, ⟨0, 0, 0, 0⟩⟩,
  ⟨⟨0, 0, 0, 0⟩, ⟨-4, 0, -4, 0⟩, ⟨4, 0, 4, 0⟩, ⟨0, 0, 0, 0⟩⟩,
  ⟨⟨4, 0, 4, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨4, 0, -4, 0⟩⟩,
  ⟨⟨0, -4, 0, 4⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 4, 0, -4⟩⟩,
  ⟨⟨0, 0, 0, 0⟩, ⟨0, 4, 0, -4⟩, ⟨0, 4, 0, 4⟩, ⟨0, 0, 0, 0⟩⟩,
  ⟨⟨0, 0, 0, 0⟩, ⟨-4, 0, 4, 0⟩, ⟨-4, 0, 4, 0⟩, ⟨0, 0, 0, 0⟩⟩,
  ⟨⟨0, 0, 0, 0⟩, ⟨0, -4, 0, -4⟩, ⟨0, -4, 0, 4⟩, ⟨0, 0, 0, 0⟩⟩,
  ⟨⟨4, 0, -4, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨-4, 0, 4, 0⟩⟩,
  ⟨⟨4, 0, 4, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨4, 0, 4, 0⟩⟩,
  ⟨⟨0, 0, 0, 0⟩, ⟨4, 0, 4, 0⟩, ⟨-4, 0, -4, 0⟩, ⟨0, 0, 0, 0⟩⟩,
  ⟨⟨0, 0, 0, 0⟩, ⟨0, 4, 0, 4⟩, ⟨0, 4, 0, 4⟩, ⟨0, 0, 0, 0⟩⟩,
  ⟨⟨0, 0, 0, 0⟩, ⟨4, 0, -4, 0⟩, ⟨4, 0, -4, 0⟩, ⟨0, 0, 0, 0⟩⟩,
  ⟨⟨0, 0, 0, 0⟩, ⟨0, 4, 0, -4⟩, ⟨0, -4, 0, 4⟩, ⟨0, 0, 0, 0⟩⟩,
  ⟨⟨0, 0, 0, 0⟩, ⟨0, -4, 0, 4⟩, ⟨0, 4, 0, -4⟩, ⟨0, 0, 0, 0⟩⟩,
  ⟨⟨0, 0, 0, 0⟩, ⟨0, -4, 0, -4⟩, ⟨0, -4, 0, -4⟩, ⟨0, 0, 0, 0⟩⟩,
  ⟨⟨0, 4, 0, 4⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, -4, 0, 4⟩⟩,
  ⟨⟨4, 0, 4, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨-4, 0, 4, 0⟩⟩,
  ⟨⟨-4, 0, 4, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨-4, 0, -4, 0⟩⟩,
  ⟨⟨0, 0, 0, 0⟩, ⟨4, 0, -4, 0⟩, ⟨4, 0, 4, 0⟩, ⟨0, 0, 0, 0⟩⟩,
  ⟨⟨0, -4, 0, 4⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 4, 0, 4⟩⟩,
  ⟨⟨0, 0, 0, 0⟩, ⟨0, -4, 0, 4⟩, ⟨0, 4, 0, 4⟩, ⟨0, 0, 0, 0⟩⟩,
  ⟨⟨0, -4, 0, -4⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 4, 0, -4⟩⟩,
  ⟨⟨0, 0, 0, 0⟩, ⟨-4, 0, -4, 0⟩, ⟨-4, 0, 4, 0⟩, ⟨0, 0, 0, 0⟩⟩,
  ⟨⟨4, 0, -4, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨-4, 0, -4, 0⟩⟩,
  ⟨⟨0, 0, 0, 0⟩, ⟨0, 4, 0, 4⟩, ⟨0, -4, 0, 4⟩, ⟨0, 0, 0, 0⟩⟩,
  ⟨⟨0, 0, 0, 0⟩, ⟨-4, 0, 4, 0⟩, ⟨-4, 0, -4, 0⟩, ⟨0, 0, 0, 0⟩⟩,
  ⟨⟨0, 0, 0, 0⟩, ⟨0, 4, 0, -4⟩, ⟨0, -4, 0, -4⟩, ⟨0, 0, 0, 0⟩⟩,
  ⟨⟨0, 0, 0, 0⟩, ⟨4, 0, 4, 0⟩, ⟨4, 0, -4, 0⟩, ⟨0, 0, 0, 0⟩⟩,
  ⟨⟨0, 0, 0, 0⟩, ⟨0, -4, 0, -4⟩, ⟨0, 4, 0, -4⟩, ⟨0, 0, 0, 0⟩⟩,
  ⟨⟨-4, 0, 4, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨4, 0, -4, 0⟩⟩,
  ⟨⟨4, 0, 4, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨-4, 0, -4, 0⟩⟩,
  ⟨⟨0, -4, 0, 4⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, -4, 0, 4⟩⟩,
  ⟨⟨0, 4, 0, 4⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, -4, 0, -4⟩⟩,
  ⟨⟨0, -4, 0, -4⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 4, 0, 4⟩⟩,
  ⟨⟨0, 0, 0, 0⟩, ⟨4, 0, 4, 0⟩, ⟨4, 0, 4, 0⟩, ⟨0, 0, 0, 0⟩⟩,
  ⟨⟨4, 0, -4, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨4, 0, -4, 0⟩⟩,
  ⟨⟨0, 0, 0, 0⟩, ⟨4, 0, -4, 0⟩, ⟨-4, 0, 4, 0⟩, ⟨0, 0, 0, 0⟩⟩,
  ⟨⟨0, 0, 0, 0⟩, ⟨-4, 0, 4, 0⟩, ⟨4, 0, -4, 0⟩, ⟨0, 0, 0, 0⟩⟩,
  ⟨⟨0, 0, 0, 0⟩, ⟨0, -4, 0, 4⟩, ⟨0, -4, 0, 4⟩, ⟨0, 0, 0, 0⟩⟩,
  ⟨⟨-4, 0, 4, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨4, 0, 4, 0⟩⟩,
  ⟨⟨0, 0, 0, 0⟩, ⟨-4, 0, -4, 0⟩, ⟨-4, 0, -4, 0⟩, ⟨0, 0, 0, 0⟩⟩,
  ⟨⟨-4, 0, -4, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨4, 0, -4, 0⟩⟩,
  ⟨⟨0, 0, 0, 0⟩, ⟨0, 4, 0, 4⟩, ⟨0, -4, 0, -4⟩, ⟨0, 0, 0, 0⟩⟩,
  ⟨⟨0, -4, 0, 4⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, -4, 0, -4⟩⟩,
  ⟨⟨0, 0, 0, 0⟩, ⟨0, 4, 0, -4⟩, ⟨0, 4, 0, -4⟩, ⟨0, 0, 0, 0⟩⟩,
  ⟨⟨0, -4, 0, -4⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, -4, 0, 4⟩⟩,
  ⟨⟨0, 4, 0, 4⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 4, 0, -4⟩⟩,
  ⟨⟨-4, 0, 4, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨-4, 0, 4, 0⟩⟩,
  ⟨⟨0, 0, 0, 0⟩, ⟨-4, 0, 4, 0⟩, ⟨4, 0, 4, 0⟩, ⟨0, 0, 0, 0⟩⟩,
  ⟨⟨-4, 0, -4, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨4, 0, 4, 0⟩⟩,
  ⟨⟨0, 0, 0, 0⟩, ⟨4, 0, 4, 0⟩, ⟨-4, 0, 4, 0⟩, ⟨0, 0, 0, 0⟩⟩,
  ⟨⟨0, -4, 0, -4⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, -4, 0, -4⟩⟩,
  ⟨⟨4, 0, -4, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨4, 0, 4, 0⟩⟩,
  ⟨⟨-4, 0, -4, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨-4, 0, 4, 0⟩⟩,
  ⟨⟨0, 0, 0, 0⟩, ⟨4, 0, -4, 0⟩, ⟨-4, 0, -4, 0⟩, ⟨0, 0, 0, 0⟩⟩,
  ⟨⟨-4, 0, -4, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨-4, 0, -4, 0⟩⟩]
def conjT (e : E8) : E8 := (Tn.mul e).mul Tdn
def CTdef : List E8 := (KsLit.filter (fun e => decide (conjT e ∈ KsLit))).map conjT
lemma c_CT : CTdef = CTLit := by decide +kernel
def SHn : E8 := Sn.mul Hn
lemma c_cov : (∀ x ∈ KsLit.map (E8.sm rt2), x ∈ CTLit.map (E8.sm rt2) ∨ x ∈ CTLit.map Hn.mul ∨
      x ∈ CTLit.map SHn.mul) ∧
    (∀ x ∈ CTLit.map (E8.sm rt2), x ∈ KsLit.map (E8.sm rt2)) ∧
    (∀ x ∈ CTLit.map Hn.mul, x ∈ KsLit.map (E8.sm rt2)) ∧
    (∀ x ∈ CTLit.map SHn.mul, x ∈ KsLit.map (E8.sm rt2)) := by decide +kernel
lemma c_dis : (∀ x ∈ CTLit.map (E8.sm rt2), x ∉ CTLit.map Hn.mul) ∧
    (∀ x ∈ CTLit.map (E8.sm rt2), x ∉ CTLit.map SHn.mul) ∧
    (∀ x ∈ CTLit.map Hn.mul, x ∉ CTLit.map SHn.mul) := by decide +kernel
lemma c_nd3 : (CTLit.map (E8.sm rt2)).Nodup ∧ (CTLit.map Hn.mul).Nodup ∧
    (CTLit.map SHn.mul).Nodup ∧ CTLit.length = 64 := by decide +kernel

noncomputable def img (n : ℕ) (L : List E8) : Set (Matrix Bool Bool ℂ) :=
  {U | ∃ e ∈ L, U = cc ^ n • φE e}

lemma img_eq_image (n : ℕ) (L : List E8) :
    img n L = (fun e => cc ^ n • φE e) '' (L.toFinset : Set E8) := by
  ext U; simp [img, eq_comm]

lemma img_finite (n : ℕ) (L : List E8) : (img n L).Finite := by
  rw [img_eq_image]; exact (Finset.finite_toSet _).image _

lemma img_ncard (n : ℕ) (L : List E8) (h : L.Nodup) : (img n L).ncard = L.length := by
  rw [img_eq_image, Set.ncard_image_of_injective _ (fun x y hxy => lvl_inj n x y hxy),
    Set.ncard_coe_finset, List.toFinset_card_of_nodup h]

lemma img_sub (n : ℕ) (L L' : List E8) (h : ∀ x ∈ L, x ∈ L') : img n L ⊆ img n L' := by
  rintro U ⟨e, he, rfl⟩; exact ⟨e, h e he, rfl⟩

lemma img_dis (n : ℕ) (L L' : List E8) (h : ∀ x ∈ L, x ∉ L') : Disjoint (img n L) (img n L') := by
  rw [Set.disjoint_left]
  rintro U ⟨e, he, rfl⟩ ⟨f, hf, hef⟩
  exact h e he (lvl_inj n e f hef ▸ hf)

lemma shift (x : E8) : cc ^ 5 • φE x = cc ^ 6 • φE (E8.sm rt2 x) := by
  rw [φE_sm, φZ_rt2, smul_smul]; congr 1; linear_combination (-(cc ^ 5)) * cc_sq

lemma img_shift (L : List E8) : img 5 L = img 6 (L.map (E8.sm rt2)) := by
  ext U; constructor
  · rintro ⟨e, he, rfl⟩; exact ⟨_, List.mem_map_of_mem he, shift e⟩
  · rintro ⟨e, he, rfl⟩
    obtain ⟨f, hf, rfl⟩ := List.mem_map.1 he
    exact ⟨f, hf, (shift f).symm⟩

lemma img_left (X : E8) (L : List E8) :
    (fun U => (cc • φE X) * U) '' img 5 L = img 6 (L.map X.mul) := by
  have key : ∀ e, (cc • φE X) * (cc ^ 5 • φE e) = cc ^ 6 • φE (X.mul e) := by
    intro e
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, φE_mul, ← pow_succ']
  ext U; constructor
  · rintro ⟨V, ⟨e, he, rfl⟩, rfl⟩; exact ⟨_, List.mem_map_of_mem he, key e⟩
  · rintro ⟨e, he, rfl⟩
    obtain ⟨f, hf, rfl⟩ := List.mem_map.1 he
    exact ⟨_, ⟨f, hf, rfl⟩, key f⟩

lemma had_eq : hadamard = cc • φE Hn := by rw [← φH]; simp [φM, H8]
lemma sh_eq : phaseS * hadamard = cc • φE SHn := by
  rw [← φH, ← φS, ← φM_mul]; simp [φM, M8.mul, S8, H8, SHn]

lemma cliff_eq : cliffordSet .hp = img 5 KsLit := by
  ext U; constructor
  · rintro ⟨w, hw, rfl⟩
    show Next46.P21.wordMatrix (chronologicalInstructions .hp w) ∈ img 5 KsLit
    rw [wm_eq w]
    exact InK_word w hw
  · rintro ⟨e, he, rfl⟩
    obtain ⟨row, hrow, rfl⟩ := Ks_mem e he
    refine ⟨row.1, c_t row hrow, ?_⟩
    show Next46.P21.wordMatrix (chronologicalInstructions .hp row.1) = _
    rw [wm_eq, key_spec 5 _ (c_k row hrow)]

lemma conj_eq (e : E8) : gateT * (cc ^ 5 • φE e) * star gateT = cc ^ 5 • φE (conjT e) := by
  rw [← φTd, ← φT]
  simp only [φM, T8, Td8, pow_zero, one_smul, conjT, φE_mul, Matrix.smul_mul, Matrix.mul_smul]

lemma ct_eq : ctSet = img 5 CTLit := by
  rw [← c_CT]
  ext U; constructor
  · rintro ⟨g, hg, hc, rfl⟩
    rw [cliff_eq] at hg hc
    obtain ⟨e, he, rfl⟩ := hg
    obtain ⟨f, hf, hfe⟩ := hc
    rw [conj_eq] at hfe ⊢
    have := lvl_inj 5 _ _ hfe
    refine ⟨conjT e, ?_, rfl⟩
    rw [CTdef, List.mem_map]
    exact ⟨e, List.mem_filter.2 ⟨he, by simpa [this] using hf⟩, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    rw [CTdef, List.mem_map] at hx
    obtain ⟨e, he, rfl⟩ := hx
    obtain ⟨he1, he2⟩ := List.mem_filter.1 he
    refine ⟨cc ^ 5 • φE e, by rw [cliff_eq]; exact ⟨e, he1, rfl⟩, ?_, ?_⟩
    · rw [conj_eq, cliff_eq]; exact ⟨_, by simpa using he2, rfl⟩
    · rw [conj_eq]

end ZW

end QAlgorithms.Papers.Independent

open QAlgorithms QAlgorithms.Papers.Independent.ZW in
/-- PDF p.7, Fact 1 and its following sentence: a disjoint union of
three left cosets, each with exactly 64 distinct exact matrices. -/
theorem solution :
    cliffordSet .hp = ctSet ∪ leftCoset hadamard ∪ leftCoset (phaseS * hadamard) ∧
    Disjoint ctSet (leftCoset hadamard) ∧
    Disjoint ctSet (leftCoset (phaseS * hadamard)) ∧
    Disjoint (leftCoset hadamard) (leftCoset (phaseS * hadamard)) ∧
    ctSet.Finite ∧ ctSet.ncard = 64 ∧
    (leftCoset hadamard).Finite ∧ (leftCoset hadamard).ncard = 64 ∧
    (leftCoset (phaseS * hadamard)).Finite ∧
      (leftCoset (phaseS * hadamard)).ncard = 64 := by
  obtain ⟨cv1, cv2, cv3, cv4⟩ := c_cov
  obtain ⟨d1, d2, d3⟩ := c_dis
  obtain ⟨n1, n2, n3, hlen⟩ := c_nd3
  have hct : ctSet = img 6 (CTLit.map (E8.sm rt2)) := by rw [ct_eq, img_shift]
  have hl1 : leftCoset hadamard = img 6 (CTLit.map Hn.mul) := by
    rw [leftCoset, ct_eq, had_eq, img_left]
  have hl2 : leftCoset (phaseS * hadamard) = img 6 (CTLit.map SHn.mul) := by
    rw [leftCoset, ct_eq, sh_eq, img_left]
  have hcl : cliffordSet .hp = img 6 (KsLit.map (E8.sm rt2)) := by rw [cliff_eq, img_shift]
  rw [hct, hl1, hl2, hcl]
  refine ⟨?_, img_dis _ _ _ d1, img_dis _ _ _ d2, img_dis _ _ _ d3, img_finite _ _, ?_,
    img_finite _ _, ?_, img_finite _ _, ?_⟩
  · apply Set.Subset.antisymm
    · rintro U ⟨e, he, rfl⟩
      rcases cv1 e he with h | h | h
      · exact Or.inl (Or.inl ⟨e, h, rfl⟩)
      · exact Or.inl (Or.inr ⟨e, h, rfl⟩)
      · exact Or.inr ⟨e, h, rfl⟩
    · exact Set.union_subset (Set.union_subset (img_sub _ _ _ cv2) (img_sub _ _ _ cv3))
        (img_sub _ _ _ cv4)
  · rw [img_ncard _ _ n1, List.length_map, hlen]
  · rw [img_ncard _ _ n2, List.length_map, hlen]
  · rw [img_ncard _ _ n3, List.length_map, hlen]



