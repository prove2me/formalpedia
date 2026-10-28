-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P10.bloch_clifford_characterization
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-22T02:55:47.967895+00:00
-- url     : https://prove2.me/submissions/c7d7f96d-6601-4a13-8177-bba9d8ab8dae

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P10

noncomputable section

namespace QAlgorithms.Papers.Independent
namespace ZW
open QAlgorithms Complex
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


set_option maxRecDepth 100000
lemma c_H : ∀ e ∈ KsLit, ∃ f ∈ KsLit, Hn.mul e = E8.sm rt2 f := by decide +kernel
lemma c_S : ∀ e ∈ KsLit, Sn.mul e ∈ KsLit := by decide +kernel
lemma c_1 : E8.scale 5 E8.one ∈ KsLit := by decide +kernel
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
def conjZ (z : Z8) : Z8 := ⟨z.a, -z.d, -z.c, -z.b⟩
def ctE (e : E8) : E8 := ⟨conjZ e.p, conjZ e.r, conjZ e.q, conjZ e.s⟩

lemma ω_conj : (starRingEnd ℂ) ω = -ω ^ 3 := by
  rw [ω3, ω_eq]; unfold sq
  simp only [map_add, map_mul, map_div₀, Complex.conj_ofReal, Complex.conj_I, map_ofNat]; ring

lemma φZ_conj (z : Z8) : star (φZ z) = φZ (conjZ z) := by
  have h2 : (starRingEnd ℂ) (ω ^ 2) = -ω ^ 2 := by
    rw [map_pow, ω_conj]; linear_combination (ω ^ 2) * ω4
  have h3 : (starRingEnd ℂ) (ω ^ 3) = -ω := by
    rw [map_pow, ω_conj]; linear_combination (-(ω ^ 5) + ω) * ω4
  show (starRingEnd ℂ) _ = _
  simp only [φZ, conjZ, map_add, map_mul, map_intCast, ω_conj, h2, h3]
  push_cast; ring

lemma φE_star (e : E8) : star (φE e) = φE (ctE e) := by
  ext i j; cases i <;> cases j <;> simp [φE, ctE, Matrix.star_apply, φZ_conj]

lemma cc_star : star cc = cc := by
  unfold cc sq; rw [star_inv₀]; congr 1; exact Complex.conj_ofReal _

lemma star_lvl (n : ℕ) (e : E8) : star (cc ^ n • φE e) = cc ^ n • φE (ctE e) := by
  rw [star_smul, star_pow, cc_star, φE_star]

/-! ## P10 Bloch part -/
open Gap48.P10

def wZ : Z8 := ⟨0, 1, 0, 0⟩
lemma φZ_wZ : φZ wZ = ω := by simp [φZ, wZ]
lemma c_W : ∀ e ∈ KsLit, E8.sm wZ e ∈ KsLit := by decide +kernel

lemma omega_eq : QAlgorithms.gateT true true = ω := by simp [gateT, ω]

lemma InK_W (U) (h : InK U) : InK (scalarOmega * U) := by
  obtain ⟨e, he, rfl⟩ := h
  refine ⟨_, c_W e he, ?_⟩
  rw [scalarOmega, omega_eq, φE_sm, φZ_wZ, Matrix.smul_mul, one_mul, smul_comm]

lemma InK_cw (w : List CliffordLetter) : InK (cliffordWordMatrix w) := by
  induction w with
  | nil => simpa [cliffordWordMatrix] using InK_one
  | cons a w ih =>
    have : cliffordWordMatrix (a :: w) = cliffordLetterMatrix a * cliffordWordMatrix w := by
      simp [cliffordWordMatrix]
    rw [this]
    cases a
    · exact InK_H _ ih
    · exact InK_S _ ih
    · exact InK_W _ ih

def cl8 : CliffordLetter → M8
  | .h => H8
  | .s => S8
  | .omega => ⟨0, E8.sm wZ E8.one⟩
def ev10 (w : List CliffordLetter) : M8 := w.foldr (fun a m => (cl8 a).mul m) M8.one

lemma cl8_spec (a : CliffordLetter) : φM (cl8 a) = cliffordLetterMatrix a := by
  cases a
  · exact φH
  · exact φS
  · show cc ^ 0 • φE (E8.sm wZ E8.one) = scalarOmega
    rw [φE_sm, φE_one, φZ_wZ, pow_zero, one_smul, scalarOmega, omega_eq]

lemma cw_eq (w : List CliffordLetter) : cliffordWordMatrix w = φM (ev10 w) := by
  induction w with
  | nil => simp [cliffordWordMatrix, ev10, φM_one]
  | cons a w ih =>
    have : cliffordWordMatrix (a :: w) = cliffordLetterMatrix a * cliffordWordMatrix w := by
      simp [cliffordWordMatrix]
    rw [this, ih]
    show _ = φM ((cl8 a).mul (ev10 w))
    rw [φM_mul, cl8_spec]

def sgE : Fin 3 → E8 := ![⟨z0, z1, z1, z0⟩, ⟨z0, ⟨0, 0, -1, 0⟩, ⟨0, 0, 1, 0⟩, z0⟩,
  ⟨z1, z0, z0, ⟨-1, 0, 0, 0⟩⟩]

lemma sg_spec (i : Fin 3) : QAlgorithms.QubitChannels.sigma i = φE (sgE i) := by
  fin_cases i <;> ext a b <;> cases a <;> cases b <;>
    simp [QAlgorithms.QubitChannels.sigma, sgE, φE, φZ, pauliX, pauliY, pauliZ, z0, z1, ω2]

def tz (e : E8) (i j : Fin 3) : Z8 :=
  let f := (((sgE i).mul e).mul (sgE j)).mul (ctE e)
  f.p.add f.s

lemma re_φZ (z : Z8) (h : z.b = z.d) : (φZ z).re = z.a := by
  have : φZ z = (z.a : ℂ) + ((z.b - z.d : ℤ) : ℂ) * (sq / 2) +
      ((((z.b + z.d : ℤ) : ℂ) * (sq / 2) + z.c) * I) := by
    rw [φZ, ω2, ω3, ω_eq]; push_cast; ring
  rw [this, h, sub_self]
  simp [sq]

lemma cc2 : cc ^ 2 = 1 / 2 := by
  unfold cc; rw [inv_pow, sq_sq]; norm_num

lemma bloch_key (e : E8) (i j : Fin 3) :
    operatorBloch (cc ^ 5 • φE e) i j = (φZ (tz e i j)).re / 64 := by
  unfold operatorBloch
  rw [star_lvl, sg_spec, sg_spec]
  have h1 : φE (sgE i) * (cc ^ 5 • φE e) * φE (sgE j) * (cc ^ 5 • φE (ctE e)) =
      (cc ^ 5 * cc ^ 5) • φE ((((sgE i).mul e).mul (sgE j)).mul (ctE e)) := by
    simp only [φE_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have ht : (φE ((((sgE i).mul e).mul (sgE j)).mul (ctE e))).trace = φZ (tz e i j) := by
    simp [Matrix.trace, φE, tz, φZ_add, add_comm]
  have hc : cc ^ 5 * cc ^ 5 = ((1 / 32 : ℝ) : ℂ) := by
    rw [← pow_add, show 5 + 5 = 2 * 5 by rfl, pow_mul, cc2]; push_cast; norm_num
  rw [h1, Matrix.trace_smul, ht, smul_eq_mul, hc, Complex.re_ofReal_mul]; ring

def good (e : E8) : Prop := ∀ i j : Fin 3, (tz e i j).b = (tz e i j).d ∧ (tz e i j).a % 64 = 0
instance (e : E8) : Decidable (good e) := by unfold good; infer_instance

def bI (e : E8) : Matrix (Fin 3) (Fin 3) ℤ := Matrix.of fun i j => (tz e i j).a / 64

def castM (W : Matrix (Fin 3) (Fin 3) ℤ) : Matrix (Fin 3) (Fin 3) ℝ := W.map (Int.cast : ℤ → ℝ)

lemma bloch_eq (e : E8) (h : good e) : operatorBloch (cc ^ 5 • φE e) = castM (bI e) := by
  ext i j
  rw [bloch_key, castM, Matrix.map_apply, bI, Matrix.of_apply, re_φZ _ (h i j).1]
  obtain ⟨k, hk⟩ : (64 : ℤ) ∣ (tz e i j).a := Int.dvd_of_emod_eq_zero (h i j).2
  rw [hk, Int.mul_ediv_cancel_left _ (by norm_num)]; push_cast; ring

def R6 : List (Fin 3 → ℤ) := [![1, 0, 0], ![-1, 0, 0], ![0, 1, 0], ![0, -1, 0], ![0, 0, 1], ![0, 0, -1]]
def LintLit : List (Matrix (Fin 3) (Fin 3) ℤ) := [
  !![1, 0, 0; 0, 1, 0; 0, 0, 1],
  !![1, 0, 0; 0, -1, 0; 0, 0, -1],
  !![1, 0, 0; 0, 0, 1; 0, -1, 0],
  !![1, 0, 0; 0, 0, -1; 0, 1, 0],
  !![-1, 0, 0; 0, 1, 0; 0, 0, -1],
  !![-1, 0, 0; 0, -1, 0; 0, 0, 1],
  !![-1, 0, 0; 0, 0, 1; 0, 1, 0],
  !![-1, 0, 0; 0, 0, -1; 0, -1, 0],
  !![0, 1, 0; 1, 0, 0; 0, 0, -1],
  !![0, 1, 0; -1, 0, 0; 0, 0, 1],
  !![0, 1, 0; 0, 0, 1; 1, 0, 0],
  !![0, 1, 0; 0, 0, -1; -1, 0, 0],
  !![0, -1, 0; 1, 0, 0; 0, 0, 1],
  !![0, -1, 0; -1, 0, 0; 0, 0, -1],
  !![0, -1, 0; 0, 0, 1; -1, 0, 0],
  !![0, -1, 0; 0, 0, -1; 1, 0, 0],
  !![0, 0, 1; 1, 0, 0; 0, 1, 0],
  !![0, 0, 1; -1, 0, 0; 0, -1, 0],
  !![0, 0, 1; 0, 1, 0; -1, 0, 0],
  !![0, 0, 1; 0, -1, 0; 1, 0, 0],
  !![0, 0, -1; 1, 0, 0; 0, -1, 0],
  !![0, 0, -1; -1, 0, 0; 0, 1, 0],
  !![0, 0, -1; 0, 1, 0; 1, 0, 0],
  !![0, 0, -1; 0, -1, 0; -1, 0, 0]]
def Words : List (List CliffordLetter) := [
  [],
  [.h, .s, .s, .h],
  [.s, .h, .s],
  [.h, .s, .h],
  [.h, .s, .s, .h, .s, .s],
  [.s, .s],
  [.s, .h, .s, .s, .s],
  [.h, .s, .h, .s, .s],
  [.s, .h, .s, .s, .h],
  [.s, .s, .s],
  [.s, .h],
  [.h, .s, .h, .s, .s, .s],
  [.s],
  [.h, .s, .s, .h, .s],
  [.s, .h, .s, .s],
  [.h, .s, .h, .s],
  [.h, .s, .s, .s],
  [.h, .s],
  [.h, .s, .s],
  [.h],
  [.s, .s, .h, .s],
  [.h, .s, .h, .s, .s, .h],
  [.s, .s, .h],
  [.s, .s, .h, .s, .s]]


instance : DecidableEq (Matrix (Fin 3) (Fin 3) ℤ) := inferInstanceAs (DecidableEq (Fin 3 → Fin 3 → ℤ))

def det3 (A : Matrix (Fin 3) (Fin 3) ℤ) : ℤ :=
  A 0 0 * A 1 1 * A 2 2 - A 0 0 * A 1 2 * A 2 1 - A 0 1 * A 1 0 * A 2 2 +
    A 0 1 * A 1 2 * A 2 0 + A 0 2 * A 1 0 * A 2 1 - A 0 2 * A 1 1 * A 2 0

lemma det3_eq (A : Matrix (Fin 3) (Fin 3) ℤ) : A.det = det3 A := Matrix.det_fin_three A

lemma c_bl : ∀ e ∈ KsLit, good e ∧ bI e ∈ LintLit := by decide +kernel
lemma c_wd : ∀ W ∈ LintLit, ∃ w ∈ Words, (ev10 w).k ≤ 5 ∧ good (keyN 5 (ev10 w)) ∧
    bI (keyN 5 (ev10 w)) = W := by decide +kernel
lemma c_LP1 : ∀ W ∈ LintLit, W * W.transpose = 1 := by decide +kernel
lemma c_LP2 : ∀ W ∈ LintLit, W.transpose * W = 1 := by decide +kernel
lemma c_LP3 : ∀ W ∈ LintLit, det3 W = 1 := by decide +kernel
def entOK (W : Matrix (Fin 3) (Fin 3) ℤ) : Bool :=
  (List.finRange 3).all fun i => (List.finRange 3).all fun j =>
    decide (W i j = -1) || decide (W i j = 0) || decide (W i j = 1)
lemma c_LP4' : ∀ W ∈ LintLit, entOK W = true := by decide +kernel
lemma c_LP4 : ∀ W ∈ LintLit, ∀ i j : Fin 3, W i j = -1 ∨ W i j = 0 ∨ W i j = 1 := by
  intro W hW i j
  have := c_LP4' W hW
  simp only [entOK, List.all_eq_true, List.mem_finRange, true_implies, Bool.or_eq_true,
    decide_eq_true_eq] at this
  rcases this i j with (h | h) | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
lemma c_LP (W) (h : W ∈ LintLit) : W * W.transpose = 1 ∧ W.transpose * W = 1 ∧ det3 W = 1 ∧
    ∀ i j, W i j = -1 ∨ W i j = 0 ∨ W i j = 1 := ⟨c_LP1 W h, c_LP2 W h, c_LP3 W h, c_LP4 W h⟩
lemma c_L6 : ∀ a ∈ R6, ∀ b ∈ R6, ∀ c ∈ R6, Matrix.of ![a, b, c] * (Matrix.of ![a, b, c]).transpose = 1 →
    det3 (Matrix.of ![a, b, c]) = 1 → Matrix.of ![a, b, c] ∈ LintLit := by decide +kernel
lemma c_nd : LintLit.Nodup := by decide +kernel
lemma c_len : LintLit.length = 24 := by decide +kernel

lemma castM_inj : Function.Injective castM :=
  Matrix.map_injective Int.cast_injective
lemma castM_mul (A B : Matrix (Fin 3) (Fin 3) ℤ) : castM (A * B) = castM A * castM B :=
  Matrix.map_mul (f := Int.castRingHom ℝ)
lemma castM_tr (A : Matrix (Fin 3) (Fin 3) ℤ) : castM A.transpose = (castM A).transpose :=
  Matrix.transpose_map.symm
lemma castM_one : castM 1 = 1 := Matrix.map_one _ Int.cast_zero Int.cast_one
lemma castM_det (A : Matrix (Fin 3) (Fin 3) ℤ) : (castM A).det = (A.det : ℝ) :=
  ((Int.castRingHom ℝ).map_det A).symm

def PP (U : RealMat) : Prop := ∀ i j, U i j = -1 ∨ U i j = 0 ∨ U i j = 1

lemma row6 (r : Fin 3 → ℤ) (hp : ∀ j, r j = -1 ∨ r j = 0 ∨ r j = 1)
    (hn : r 0 * r 0 + r 1 * r 1 + r 2 * r 2 = 1) : r ∈ R6 := by
  have hr : r = ![r 0, r 1, r 2] := by funext j; fin_cases j <;> rfl
  rw [hr]
  rcases hp 0 with h0 | h0 | h0 <;> rcases hp 1 with h1 | h1 | h1 <;>
    rcases hp 2 with h2 | h2 | h2 <;> rw [h0, h1, h2] at hn ⊢ <;>
    first | (norm_num at hn; done) | decide

lemma inR_iff (U : RealMat) : (∃ W ∈ LintLit, castM W = U) ↔ SpecialOrthogonal U ∧ PP U := by
  constructor
  · rintro ⟨W, hW, rfl⟩
    obtain ⟨h1, h2, h3, h4⟩ := c_LP W hW
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · rw [← castM_tr, ← castM_mul, h2, castM_one]
    · rw [← castM_tr, ← castM_mul, h1, castM_one]
    · rw [castM_det, det3_eq, h3]; simp
    · intro i j
      rcases h4 i j with h | h | h <;> simp [castM, h]
  · rintro ⟨⟨_, hUU, hdet⟩, hP⟩
    let W : Matrix (Fin 3) (Fin 3) ℤ := Matrix.of fun i j =>
      if U i j = -1 then -1 else if U i j = 0 then 0 else 1
    have hWU : castM W = U := by
      ext i j
      simp only [castM, Matrix.map_apply, W, Matrix.of_apply]
      rcases hP i j with h | h | h <;> simp [h] <;> norm_num
    have hWW : W * W.transpose = 1 := castM_inj (by rw [castM_mul, castM_tr, hWU, hUU, castM_one])
    have hWd : det3 W = 1 := by
      rw [← det3_eq]; exact_mod_cast (castM_det W).symm.trans (hWU ▸ hdet)
    have hWP : ∀ i j, W i j = -1 ∨ W i j = 0 ∨ W i j = 1 := by
      intro i j; simp only [W, Matrix.of_apply]; split_ifs <;> simp
    have hrow : ∀ i, W i ∈ R6 := by
      intro i
      apply row6 _ (hWP i)
      have := congrFun (congrFun hWW i) i
      simpa [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply] using this
    have hWr : W = Matrix.of ![W 0, W 1, W 2] := by
      ext i j; fin_cases i <;> rfl
    refine ⟨W, ?_, hWU⟩
    rw [hWr] at hWW hWd ⊢
    exact c_L6 _ (hrow 0) _ (hrow 1) _ (hrow 2) hWW hWd

lemma rownorm (U : RealMat) (h : U * U.transpose = 1) (i : Fin 3) :
    U i 0 * U i 0 + U i 1 * U i 1 + U i 2 * U i 2 = 1 := by
  have := congrFun (congrFun h i) i
  simpa [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply] using this

lemma mv3 (U : RealMat) (x : Fin 3 → ℝ) (i : Fin 3) :
    U.mulVec x i = U i 0 * x 0 + U i 1 * x 1 + U i 2 * x 2 := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

lemma absP (u : ℝ) (h : u = -1 ∨ u = 0 ∨ u = 1) : |u| = u * u := by
  rcases h with h | h | h <;> subst h <;> norm_num

lemma cubeA (U : RealMat) (h : U * U.transpose = 1) :
    (∀ x ∈ cube, U.mulVec x ∈ cube) ↔ PP U := by
  constructor
  · intro hc i
    have hn := rownorm U h i
    let x : Fin 3 → ℝ := fun j => if 0 ≤ U i j then 1 else -1
    have hx : x ∈ cube := by
      intro j; simp only [x]; split_ifs <;> norm_num
    have hux := (hc x hx i).2
    rw [mv3] at hux
    have hs : ∀ j, U i j * x j = |U i j| := by
      intro j; simp only [x]; split_ifs with hj
      · rw [abs_of_nonneg hj]; ring
      · rw [abs_of_neg (not_le.mp hj)]; ring
    rw [hs, hs, hs] at hux
    have e0 := sq_abs (U i 0); have e1 := sq_abs (U i 1); have e2 := sq_abs (U i 2)
    have p0 := abs_nonneg (U i 0); have p1 := abs_nonneg (U i 1); have p2 := abs_nonneg (U i 2)
    have k : ∀ j, |U i j| * |U i j| = |U i j| := by
      intro j
      fin_cases j <;> simp <;> nlinarith
    intro j
    have := k j
    have : |U i j| = 0 ∨ |U i j| = 1 := by
      have : |U i j| * (|U i j| - 1) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · exact Or.inl h
      · exact Or.inr (by linarith)
    rcases this with h0 | h1
    · right; left; exact abs_eq_zero.mp h0
    · rcases abs_eq (zero_le_one) |>.mp h1 with h | h
      · right; right; exact h
      · left; exact h
  · intro hP x hx i
    have hn := rownorm U h i
    rw [mv3]
    have b : ∀ j, |U i j * x j| ≤ U i j * U i j := by
      intro j
      rw [abs_mul, ← absP _ (hP i j)]
      exact mul_le_of_le_one_right (abs_nonneg _) (abs_le.mpr (hx j))
    have t := abs_add_three (U i 0 * x 0) (U i 1 * x 1) (U i 2 * x 2)
    have := abs_le.mp (le_trans t (by linarith [b 0, b 1, b 2]) :
      |U i 0 * x 0 + U i 1 * x 1 + U i 2 * x 2| ≤ 1)
    exact ⟨this.1, this.2⟩

lemma cubeC (U : RealMat) (hS : SpecialOrthogonal U) :
    Set.image (fun x => U.mulVec x) cube = cube ↔ PP U := by
  obtain ⟨h1, h2, _⟩ := hS
  constructor
  · intro hi
    rw [← cubeA U h2]
    intro x hx; rw [← hi]; exact ⟨x, hx, rfl⟩
  · intro hP
    have hA := (cubeA U h2).mpr hP
    have hPt : PP U.transpose := fun i j => hP j i
    have hAt := (cubeA U.transpose (by rw [Matrix.transpose_transpose]; exact h1)).mpr hPt
    ext y; constructor
    · rintro ⟨x, hx, rfl⟩; exact hA x hx
    · intro hy
      refine ⟨U.transpose.mulVec y, hAt y hy, ?_⟩
      simp only [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]

lemma bloch_iff (V : RealMat) :
    (∃ C : Clifford, operatorBloch C.val = V) ↔ ∃ W ∈ LintLit, castM W = V := by
  constructor
  · rintro ⟨⟨C, w, rfl⟩, rfl⟩
    obtain ⟨e, he, hCe⟩ := InK_cw w
    obtain ⟨hg, hm⟩ := c_bl e he
    exact ⟨_, hm, by simp only; rw [hCe, bloch_eq e hg]⟩
  · rintro ⟨W, hW, rfl⟩
    obtain ⟨w, -, hk, hg, hb⟩ := c_wd W hW
    refine ⟨cliffordOfWord w, ?_⟩
    show operatorBloch (cliffordWordMatrix w) = _
    rw [cw_eq, key_spec 5 _ hk, bloch_eq _ hg, hb]

end ZW
end QAlgorithms.Papers.Independent

open scoped Classical in
open QAlgorithms.Papers.Independent.Gap48.P10 QAlgorithms.Papers.Independent.ZW in
theorem solution :
    Nat.card {V : RealMat // ∃ C : Clifford, operatorBloch C.val = V} = 24 ∧
    ∀ U : RealMat,
      ((∃ C : Clifford, operatorBloch C.val = U) ↔
        SpecialOrthogonal U ∧ ∀ i j, U i j = -1 ∨ U i j = 0 ∨ U i j = 1) ∧
      ((∃ C : Clifford, operatorBloch C.val = U) ↔
        SpecialOrthogonal U ∧ Set.image (fun x => U.mulVec x) cube = cube) := by
  refine ⟨?_, fun U => ⟨(bloch_iff U).trans (inR_iff U), ?_⟩⟩
  · rw [Nat.card_congr (Equiv.subtypeEquivRight bloch_iff)]
    have hS : {V : RealMat | ∃ W ∈ LintLit, castM W = V} =
        ((LintLit.map castM).toFinset : Set RealMat) := by
      ext V; simp
    change Nat.card ↥{V : RealMat | ∃ W ∈ LintLit, castM W = V} = 24
    rw [hS, Nat.card_coe_set_eq, Set.ncard_coe_finset,
      List.toFinset_card_of_nodup (c_nd.map castM_inj), List.length_map, c_len]
  · rw [bloch_iff, inR_iff]
    constructor
    · rintro ⟨hS, hP⟩; exact ⟨hS, (cubeC U hS).mpr hP⟩
    · rintro ⟨hS, hc⟩; exact ⟨hS, (cubeC U hS).mp hc⟩

