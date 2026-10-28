-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P07.orthogonal_negativity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T08:34:22.541316+00:00
-- url     : https://prove2.me/submissions/46f783d0-5a6f-48c6-bd6e-0b6fbd56a1bf

import Definitions.Def_QAlgorithms_Defs_EntanglementNegativity
import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
import Definitions.Def_QAlgorithms_Defs_QuditChannelFidelities
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P07_Model
set_option autoImplicit false

noncomputable section

open scoped Matrix ComplexOrder NNReal ENNReal

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Independent1.P07

open Entanglement

open Matrix

structure ON_Proj {n : Type*} [Fintype n] [DecidableEq n] (P1 P2 P3 : Matrix n n ℂ) : Prop where
  h11 : P1 * P1 = P1
  h22 : P2 * P2 = P2
  h33 : P3 * P3 = P3
  h12 : P1 * P2 = 0
  h13 : P1 * P3 = 0
  h21 : P2 * P1 = 0
  h23 : P2 * P3 = 0
  h31 : P3 * P1 = 0
  h32 : P3 * P2 = 0
  hsum : P1 + P2 + P3 = 1
  s1 : P1ᴴ = P1
  s2 : P2ᴴ = P2
  s3 : P3ᴴ = P3

lemma ON_mul {n : Type*} [Fintype n] [DecidableEq n] {P1 P2 P3 : Matrix n n ℂ}
    (h : ON_Proj P1 P2 P3) (a1 a2 a3 b1 b2 b3 : ℝ) :
    (a1 • P1 + a2 • P2 + a3 • P3) * (b1 • P1 + b2 • P2 + b3 • P3)
      = (a1 * b1) • P1 + (a2 * b2) • P2 + (a3 * b3) • P3 := by
  simp only [add_mul, mul_add, smul_mul_smul, h.h11, h.h22, h.h33, h.h12, h.h13, h.h21, h.h23,
    h.h31, h.h32, smul_zero, add_zero, zero_add]

lemma ON_sa {n : Type*} [Fintype n] [DecidableEq n] {P1 P2 P3 : Matrix n n ℂ}
    (h : ON_Proj P1 P2 P3) (a1 a2 a3 : ℝ) :
    (a1 • P1 + a2 • P2 + a3 • P3)ᴴ = a1 • P1 + a2 • P2 + a3 • P3 := by
  simp [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, h.s1, h.s2, h.s3]

lemma ON_aeval {n : Type*} [Fintype n] [DecidableEq n] {P1 P2 P3 : Matrix n n ℂ}
    (h : ON_Proj P1 P2 P3) (μ1 μ2 μ3 : ℝ) (p : Polynomial ℝ) :
    Polynomial.aeval (μ1 • P1 + μ2 • P2 + μ3 • P3) p
      = (p.eval μ1) • P1 + (p.eval μ2) • P2 + (p.eval μ3) • P3 := by
  induction p using Polynomial.induction_on with
  | C a =>
    simp only [Polynomial.aeval_C, Polynomial.eval_C, Algebra.algebraMap_eq_smul_one, ← h.hsum,
      smul_add]
  | add p q hp hq =>
    rw [map_add, hp, hq]
    simp only [Polynomial.eval_add, add_smul]; abel
  | monomial m a ih =>
    rw [pow_succ, ← mul_assoc, map_mul, ih, Polynomial.aeval_X, ON_mul h]
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X,
      mul_assoc]

lemma ON_spectrum {n : Type*} [Fintype n] [DecidableEq n] {P1 P2 P3 : Matrix n n ℂ}
    (h : ON_Proj P1 P2 P3) (μ1 μ2 μ3 : ℝ) (x : ℝ)
    (hx : x ∈ spectrum ℝ (μ1 • P1 + μ2 • P2 + μ3 • P3)) : x = μ1 ∨ x = μ2 ∨ x = μ3 := by
  set q : Polynomial ℝ := (Polynomial.X - Polynomial.C μ1) * (Polynomial.X - Polynomial.C μ2) *
    (Polynomial.X - Polynomial.C μ3) with hq
  have h0 : Polynomial.aeval (μ1 • P1 + μ2 • P2 + μ3 • P3) q = 0 := by
    rw [ON_aeval h]; simp [hq]
  have hmem := spectrum.subset_polynomial_aeval (μ1 • P1 + μ2 • P2 + μ3 • P3) q ⟨x, hx, rfl⟩
  rw [h0] at hmem
  have hev : q.eval x = 0 := by
    by_contra hne
    apply spectrum.notMem_iff.mpr _ hmem
    simpa using (IsUnit.mk0 _ hne).map (algebraMap ℝ (Matrix n n ℂ))
  simp only [hq, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_C,
    mul_eq_zero, sub_eq_zero] at hev
  tauto

lemma ON_cfc {n : Type*} [Fintype n] [DecidableEq n] {P1 P2 P3 : Matrix n n ℂ}
    (h : ON_Proj P1 P2 P3) (μ1 μ2 μ3 : ℝ) (f : ℝ → ℝ) :
    cfc f (μ1 • P1 + μ2 • P2 + μ3 • P3) = f μ1 • P1 + f μ2 • P2 + f μ3 • P3 := by
  classical
  set s : Finset ℝ := {μ1, μ2, μ3}
  set p : Polynomial ℝ := Lagrange.interpolate s id f
  have hp : ∀ x ∈ s, p.eval x = f x := fun x hx =>
    Lagrange.eval_interpolate_at_node (v := id) f (Set.injOn_id _) hx
  have hA : IsSelfAdjoint (μ1 • P1 + μ2 • P2 + μ3 • P3) := ON_sa h μ1 μ2 μ3
  rw [cfc_congr (g := fun x => p.eval x) (a := μ1 • P1 + μ2 • P2 + μ3 • P3)]
  · rw [cfc_polynomial p _ hA, ON_aeval h, hp μ1 (by simp [s]), hp μ2 (by simp [s]),
      hp μ3 (by simp [s])]
  · intro x hx
    refine (hp x ?_).symm
    rcases ON_spectrum h μ1 μ2 μ3 x hx with h | h | h <;> simp [s, h]

lemma ON_traceNorm {n : Type*} [Fintype n] [DecidableEq n] {P1 P2 P3 : Matrix n n ℂ}
    (h : ON_Proj P1 P2 P3) (μ1 μ2 μ3 : ℝ) :
    traceNorm (μ1 • P1 + μ2 • P2 + μ3 • P3) =
      |μ1| * P1.trace.re + |μ2| * P2.trace.re + |μ3| * P3.trace.re := by
  rw [traceNorm, ON_sa h, ON_mul h, ON_cfc h]
  simp only [Real.sqrt_mul_self_eq_abs, Matrix.trace_add, Matrix.trace_smul, Complex.add_re,
    Complex.real_smul, Complex.re_ofReal_mul]


def ON_Phi (d : ℕ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  Matrix.of fun p q => (if p.1 = p.2 then 1 else 0) * (if q.1 = q.2 then 1 else 0) * ((d : ℂ)⁻¹)

lemma ON_singlet {d : ℕ} (hd : 0 < d) : singlet d hd = ON_Phi d := by
  ext p q
  simp only [singlet, pureDensity, finiteMaxEntangled, ON_Phi, Matrix.of_apply, Fintype.card_fin]
  have hs : ((Real.sqrt d : ℂ))⁻¹ * ((Real.sqrt d : ℂ))⁻¹ = (d : ℂ)⁻¹ := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _)]; simp
  split_ifs <;> simp [hs]

lemma ON_Phi_mul_Phi {d : ℕ} (hd : 0 < d) : ON_Phi d * ON_Phi d = ON_Phi d := by
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  ext p q
  simp only [ON_Phi, Matrix.mul_apply, Matrix.of_apply, Fintype.sum_prod_type]
  simp [Finset.sum_ite_eq, Finset.sum_mul, Finset.mul_sum]
  split_ifs <;> field_simp

lemma ON_F_mul_Phi {d : ℕ} : (swapOp : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) * ON_Phi d = ON_Phi d := by
  ext p q
  simp only [ON_Phi, swapOp, Matrix.mul_apply, Matrix.of_apply, Fintype.sum_prod_type, Prod.ext_iff]
  simp [Finset.sum_ite_eq, Finset.sum_mul, Finset.mul_sum, ite_and]
  split_ifs <;> simp_all [eq_comm]

lemma ON_Phi_mul_F {d : ℕ} : ON_Phi d * (swapOp : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) = ON_Phi d := by
  ext p q
  simp only [ON_Phi, swapOp, Matrix.mul_apply, Matrix.of_apply, Fintype.sum_prod_type, Prod.ext_iff]
  simp [Finset.sum_ite_eq, Finset.sum_mul, Finset.mul_sum, ite_and]
  split_ifs <;> simp_all [eq_comm]

lemma ON_F_mul_F {d : ℕ} : (swapOp : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) * swapOp = 1 := by
  ext p q
  simp only [swapOp, Matrix.mul_apply, Matrix.of_apply, Fintype.sum_prod_type, Prod.ext_iff,
    Matrix.one_apply]
  simp [ite_and]

lemma ON_Phi_sa {d : ℕ} : (ON_Phi d)ᴴ = ON_Phi d := by
  ext p q; simp [ON_Phi, Matrix.conjTranspose_apply]; split_ifs <;> simp

lemma ON_F_sa {d : ℕ} : (swapOp : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)ᴴ = swapOp := by
  ext p q; simp only [swapOp, Matrix.conjTranspose_apply, Matrix.of_apply, Prod.ext_iff]
  split_ifs <;> simp_all [eq_comm]

lemma ON_tr_Phi {d : ℕ} (hd : 0 < d) : (ON_Phi d).trace = 1 := by
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  simp [ON_Phi, Matrix.trace, Fintype.sum_prod_type, Finset.sum_ite_eq]
  field_simp

lemma ON_tr_F {d : ℕ} : (swapOp : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ).trace = d := by
  simp [swapOp, Matrix.trace, Fintype.sum_prod_type, Prod.ext_iff, ite_and, Finset.sum_ite_eq]

lemma ON_tr_one {d : ℕ} : (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ).trace = (d : ℂ)^2 := by
  simp [Matrix.trace_one]; ring

lemma ON_PT {d : ℕ} (hd : 0 < d) (a b c : ℝ) :
    partialTransposeFirst (orthogonalFamily d hd a b c) =
      a • (swapOp : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) + (b * d) • ON_Phi d + c • 1 := by
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  ext p q
  simp only [partialTransposeFirst, orthogonalFamily, ON_singlet, ON_Phi, swapOp, Matrix.of_apply,
    Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Prod.ext_iff, Complex.real_smul,
    smul_eq_mul]
  obtain ⟨i, j⟩ := p
  obtain ⟨k, l⟩ := q
  simp only [ite_and]
  push_cast
  split_ifs <;> subst_vars <;> simp_all

lemma ON_proj {d : ℕ} (hd : 0 < d) :
    ON_Proj (ON_Phi d) ((1/2 : ℝ) • (1 + swapOp) - ON_Phi d) ((1/2 : ℝ) • (1 - swapOp)) := by
  have h1 := ON_Phi_mul_Phi hd
  have h2 := @ON_F_mul_Phi d
  have h3 := @ON_Phi_mul_F d
  have h4 := @ON_F_mul_F d
  refine ⟨h1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ON_Phi_sa, ?_, ?_⟩ <;>
  (try simp only [mul_sub, sub_mul, mul_add, add_mul, smul_mul_smul, smul_mul_assoc, mul_smul_comm,
    one_mul, mul_one, h1, h2, h3, h4, Matrix.conjTranspose_sub, Matrix.conjTranspose_add,
    Matrix.conjTranspose_smul, Matrix.conjTranspose_one, ON_Phi_sa, ON_F_sa, star_trivial]) <;>
  module

lemma ON_tr_P2 {d : ℕ} (hd : 0 < d) :
    ((1/2 : ℝ) • (1 + swapOp) - ON_Phi d : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ).trace.re
      = ((d:ℝ)^2 + d)/2 - 1 := by
  simp [Matrix.trace_sub, Matrix.trace_add, Matrix.trace_smul, ON_tr_Phi hd, ON_tr_F, ON_tr_one]
  ring

lemma ON_tr_P3 {d : ℕ} :
    ((1/2 : ℝ) • (1 - swapOp) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ).trace.re
      = ((d:ℝ)^2 - d)/2 := by
  simp [Matrix.trace_sub, Matrix.trace_smul, ON_tr_F, ON_tr_one]
  ring

lemma ON_rho {d : ℕ} (hd : 0 < d) (a b c : ℝ) :
    orthogonalFamily d hd a b c = (a * d) • ON_Phi d + b • swapOp + c • 1 := by
  simp only [orthogonalFamily, ON_singlet, Complex.coe_smul]

lemma ON_main {d : ℕ} (hd : 0 < d) (a b c : ℝ)
    (hrho : IsDensityMatrix (orthogonalFamily d hd a b c)) :
    negativity (orthogonalFamily d hd a b c) =
      |1 - orthogonalF hd (orthogonalFamily d hd a b c)|/4
      + |1 + orthogonalF hd (orthogonalFamily d hd a b c)
          - 2 * orthogonalG (orthogonalFamily d hd a b c)/(d : ℝ)|/4
      + |orthogonalG (orthogonalFamily d hd a b c)/(d : ℝ)|/2 - 1/2 := by
  have hX : partialTransposeFirst (orthogonalFamily d hd a b c) =
      (a + b * d + c) • ON_Phi d + (a + c) • ((1/2 : ℝ) • (1 + swapOp) - ON_Phi d)
        + (c - a) • ((1/2 : ℝ) • (1 - swapOp)) := by
    rw [ON_PT]; module
  have htr := congrArg Complex.re hrho.2
  rw [ON_rho] at htr
  simp [Matrix.trace_add, Matrix.trace_smul, ON_tr_Phi hd, ON_tr_F, ON_tr_one] at htr
  have hf : orthogonalF hd (orthogonalFamily d hd a b c) = d * (a * d + b + c) := by
    rw [orthogonalF, ON_singlet hd, ON_rho]
    simp [add_mul, smul_mul_assoc, ON_Phi_mul_Phi hd, ON_F_mul_Phi, Matrix.trace_add,
      Matrix.trace_smul, ON_tr_Phi hd]
  have hg : orthogonalG (orthogonalFamily d hd a b c) = a * d + b * (d * d) + c * d := by
    rw [orthogonalG, ON_rho]
    simp [add_mul, smul_mul_assoc, ON_Phi_mul_F, ON_F_mul_F, Matrix.trace_add,
      Matrix.trace_smul, ON_tr_Phi hd, ON_tr_F, ON_tr_one]
  rw [negativity, hX, ON_traceNorm (ON_proj hd), ON_tr_P2 hd, ON_tr_P3, hf, hg]
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  have e1 : 1 - d * (a * d + b + c) = 2 * (((d:ℝ)^2 - d)/2) * (c - a) := by
    linear_combination (-1) * htr
  have e3 : (a * d + b * (d * d) + c * d) / d = a + b * d + c := by
    field_simp
  have e2 : 1 + d * (a * d + b + c) - 2 * (a * d + b * (d * d) + c * d) / d
      = 2 * (((d:ℝ)^2 + d)/2 - 1) * (a + c) := by
    rw [mul_div_assoc, e3]
    linear_combination (-1) * htr
  have m2 : 0 ≤ ((d:ℝ)^2 + d)/2 - 1 := by nlinarith
  have m3 : 0 ≤ ((d:ℝ)^2 - d)/2 := by nlinarith
  rw [e1, e2, e3, abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg m2, abs_of_nonneg m3,
    ON_tr_Phi hd, Complex.one_re]
  norm_num
  ring

end QAlgorithms.Papers.Independent.Independent1.P07

open QAlgorithms QAlgorithms.Entanglement QAlgorithms.Papers.Independent.Independent1.P07 in
/-- Eqs. (51)–(52), PDF p. 8, including d = 1. -/
theorem solution {d : ℕ} (hd : 0 < d) (a b c : ℝ)
    (hrho : IsDensityMatrix (orthogonalFamily d hd a b c)) :
    let rho := orthogonalFamily d hd a b c
    let f := orthogonalF hd rho
    let g := orthogonalG rho
    negativity rho = |1-f|/4+|1+f-2*g/(d : ℝ)|/4+|g/(d : ℝ)|/2-1/2 := by
  intro rho f g
  exact ON_main hd a b c hrho
