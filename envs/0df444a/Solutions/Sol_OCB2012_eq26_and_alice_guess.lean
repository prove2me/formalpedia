-- Prove2me | solution 1 for OCB2012.eq26_and_alice_guess
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-08T23:14:20.730337+00:00
-- url     : https://prove2.me/submissions/157592b8-e5af-4c70-83ab-103b449253c5

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics
import Definitions.Def_OCB2012_defs

open Matrix
open scoped Kronecker ComplexOrder

namespace OCB2012Sol
open OCB2012

lemma σz_mul_σz : σz * σz = 1 := by
  rw [σz, mul_fin_two, one_fin_two]; norm_num

lemma σx_mul_σx : σx * σx = 1 := by
  rw [σx, mul_fin_two, one_fin_two]; norm_num

lemma trace_σz : σz.trace = 0 := by simp [σz, trace_fin_two]

lemma trace_σx : σx.trace = 0 := by simp [σx, trace_fin_two]

lemma trace_σz_mul_σx : (σz * σx).trace = 0 := by
  simp [σz, σx, trace_fin_two]

lemma trace_σx_mul_σz : (σx * σz).trace = 0 := by
  simp [σz, σx, trace_fin_two]

lemma trace_one_qubit : (1 : Matrix Qubit Qubit ℂ).trace = 2 := by
  simp [trace_one]

/-- Traces of Pauli strings against the local operators `𝟙 + s σ`. -/
lemma tr_1z (s : ℂ) : (1 + s • σz).trace = 2 := by
  rw [trace_add, trace_smul, trace_σz, trace_one_qubit]; simp
lemma tr_1x (s : ℂ) : (1 + s • σx).trace = 2 := by
  rw [trace_add, trace_smul, trace_σx, trace_one_qubit]; simp
lemma tr_z1z (s : ℂ) : (σz * (1 + s • σz)).trace = 2 * s := by
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, σz_mul_σz, trace_add, trace_smul,
    trace_σz, trace_one_qubit]; simp; ring
lemma tr_x1x (s : ℂ) : (σx * (1 + s • σx)).trace = 2 * s := by
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, σx_mul_σx, trace_add, trace_smul,
    trace_σx, trace_one_qubit]; simp; ring
lemma tr_x1z (s : ℂ) : (σx * (1 + s • σz)).trace = 0 := by
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, trace_add, trace_smul,
    trace_σx, trace_σx_mul_σz]; simp
lemma tr_z1x (s : ℂ) : (σz * (1 + s • σx)).trace = 0 := by
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, trace_add, trace_smul,
    trace_σz, trace_σz_mul_σx]; simp

variable {a1 a2 b1 b2 : Type*} [Fintype a1] [Fintype a2] [Fintype b1] [Fintype b2]

lemma prob_add_W (W W' : Matrix ((a1 × a2) × (b1 × b2)) ((a1 × a2) × (b1 × b2)) ℂ)
    (MA : Matrix (a1 × a2) (a1 × a2) ℂ) (MB : Matrix (b1 × b2) (b1 × b2) ℂ) :
    prob (W + W') MA MB = prob W MA MB + prob W' MA MB := by
  simp only [prob, Matrix.add_mul, trace_add]

lemma prob_smul_W (r : ℂ) (W : Matrix ((a1 × a2) × (b1 × b2)) ((a1 × a2) × (b1 × b2)) ℂ)
    (MA : Matrix (a1 × a2) (a1 × a2) ℂ) (MB : Matrix (b1 × b2) (b1 × b2) ℂ) :
    prob (r • W) MA MB = r * prob W MA MB := by
  simp only [prob, Matrix.smul_mul, trace_smul, smul_eq_mul]

lemma prob_smul_A (r : ℂ) (W : Matrix ((a1 × a2) × (b1 × b2)) ((a1 × a2) × (b1 × b2)) ℂ)
    (MA : Matrix (a1 × a2) (a1 × a2) ℂ) (MB : Matrix (b1 × b2) (b1 × b2) ℂ) :
    prob W (r • MA) MB = r * prob W MA MB := by
  simp only [prob, smul_kronecker, Matrix.mul_smul, trace_smul, smul_eq_mul]

lemma prob_smul_B (r : ℂ) (W : Matrix ((a1 × a2) × (b1 × b2)) ((a1 × a2) × (b1 × b2)) ℂ)
    (MA : Matrix (a1 × a2) (a1 × a2) ℂ) (MB : Matrix (b1 × b2) (b1 × b2) ℂ) :
    prob W MA (r • MB) = r * prob W MA MB := by
  simp only [prob, kronecker_smul, Matrix.mul_smul, trace_smul, smul_eq_mul]

/-- For product operators, the probability factorizes into four local traces. -/
lemma prob_kron4 (P1 A1 : Matrix a1 a1 ℂ) (P2 A2 : Matrix a2 a2 ℂ) (P3 B1 : Matrix b1 b1 ℂ)
    (P4 B2 : Matrix b2 b2 ℂ) :
    prob ((P1 ⊗ₖ P2) ⊗ₖ (P3 ⊗ₖ P4)) (A1 ⊗ₖ A2) (B1 ⊗ₖ B2) =
      (P1 * A1).trace * (P2 * A2).trace * ((P3 * B1).trace * (P4 * B2).trace) := by
  simp only [prob, ← mul_kronecker_mul, trace_kronecker]

/-- Joint probabilities of the protocol of Appendix E on the process (7):
`P(x, y | a, b, b' = 1) = ¼ [1 + (-1)^{a+y}/√2]` and
`P(x, y | a, b, b' = 0) = ¼ [1 + (-1)^{x+b}/√2]`, for any `ρ` with `Tr ρ = 1`. -/
lemma prob_W7_ξ_η (ρ : Matrix Qubit Qubit ℂ) (hρ : ρ.trace = 1) (x a y b b' : Bool) :
    prob W7 (ξ x a) (η ρ y b b') =
      if b' then (1 / 4 : ℂ) * (1 + ((1 / Real.sqrt 2 : ℝ) : ℂ) * (sgn a * sgn y))
      else (1 / 4 : ℂ) * (1 + ((1 / Real.sqrt 2 : ℝ) : ℂ) * (sgn x * sgn b)) := by
  have hW : W7 = (1 / 4 : ℂ) • ((((1 : Matrix Qubit Qubit ℂ) ⊗ₖ (1 : Matrix Qubit Qubit ℂ)) ⊗ₖ
      ((1 : Matrix Qubit Qubit ℂ) ⊗ₖ (1 : Matrix Qubit Qubit ℂ))) +
      ((1 / Real.sqrt 2 : ℝ) : ℂ) •
        ((((1 : Matrix Qubit Qubit ℂ) ⊗ₖ σz) ⊗ₖ (σz ⊗ₖ (1 : Matrix Qubit Qubit ℂ))) +
         ((σz ⊗ₖ (1 : Matrix Qubit Qubit ℂ)) ⊗ₖ (σx ⊗ₖ σz)))) := by
    simp only [W7, one_kronecker_one]
  have hsxz : sgn (xor b y) = sgn b * sgn y := by
    cases b <;> cases y <;> simp [sgn]
  have hyy : sgn y * sgn y = 1 := by cases y <;> simp [sgn]
  rw [hW, ξ]
  cases b'
  · simp only [η, Bool.false_eq_true, if_false]
    simp only [prob_smul_W, prob_add_W, prob_smul_A, prob_smul_B, prob_kron4, Matrix.one_mul,
      tr_1z, tr_1x, tr_z1z, tr_x1x, tr_z1x, hsxz]
    linear_combination (1 / 4 * ((1 / Real.sqrt 2 : ℝ) : ℂ) * (sgn x * sgn b)) * hyy
  · simp only [η, if_true]
    simp only [prob_smul_W, prob_add_W, prob_smul_A, prob_smul_B, prob_kron4, Matrix.one_mul,
      tr_1z, tr_z1z, tr_x1z, hρ]
    ring

end OCB2012Sol

open OCB2012 OCB2012Sol in
theorem solution (ρ : Matrix Qubit Qubit ℂ) (hρ : PeresTerno.IsDensityMatrix ρ) :
    (∀ a b y : Bool, ∑ x : Bool, prob W7 (ξ x a) (η ρ y b true) =
        (((1 / 2 : ℝ) * (1 + (if xor y a then -1 else 1) / Real.sqrt 2) : ℝ) : ℂ)) ∧
    (1 / 4 : ℂ) * ∑ a : Bool, ∑ b : Bool, ∑ y : Bool, prob W7 (ξ b a) (η ρ y b false) =
        (((2 + Real.sqrt 2) / 4 : ℝ) : ℂ) := by
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  refine ⟨fun a b y => ?_, ?_⟩
  · simp only [Fintype.sum_bool, prob_W7_ξ_η ρ hρ.2, if_true]
    cases a <;> cases y <;> simp [sgn] <;> field_simp <;> ring
  · simp only [Fintype.sum_bool, prob_W7_ξ_η ρ hρ.2, Bool.false_eq_true, if_false]
    have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
    simp [sgn]; field_simp; ring_nf
    linear_combination (-4 : ℂ) * h2
