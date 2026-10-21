-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P48.adc_dilation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T09:16:58.803381+00:00
-- url     : https://prove2.me/submissions/3bd864a2-b442-41db-929c-25c6bd4b11b9

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P48

noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P48

namespace G56D

def P : QQOp := pairMatrix !![1, 0, 0, 0; 0, 1, 1, 0; 0, Complex.I, -Complex.I, 0; 0, 0, 0, 1]
def Q : QQOp := pairMatrix !![1, 0, 0, 0; 0, 1/2, -Complex.I/2, 0; 0, 1/2, Complex.I/2, 0; 0, 0, 0, 1]

lemma PQ : P * Q = 1 := by
  ext ⟨a, b⟩ ⟨c, d⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [P, Q, pairMatrix, pairIndex, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring

lemma QP : Q * P = 1 := by
  ext ⟨a, b⟩ ⟨c, d⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [P, Q, pairMatrix, pairIndex, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring

def u : (QQOp)ˣ := ⟨P, Q, PQ, QP⟩

def dv (θ : ℝ) : Bool × Bool → ℂ := fun p =>
  if p = (false, true) then (θ : ℂ) * Complex.I else if p = (true, false) then -((θ : ℂ) * Complex.I) else 0

lemma gen_eq (θ : ℝ) : (-Complex.I * (θ : ℂ)) • adcDilationGenerator = P * Matrix.diagonal (dv θ) * Q := by
  ext ⟨a, b⟩ ⟨c, d⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [P, Q, dv, pairMatrix, pairIndex, Matrix.mul_apply, Fintype.sum_prod_type, adcDilationGenerator,
      Matrix.kronecker, pauliX, pauliY, Matrix.diagonal_apply] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring

lemma exp_eq (θ : ℝ) : NormedSpace.exp ((-Complex.I * (θ : ℂ)) • adcDilationGenerator) = adcUnitary θ := by
  rw [gen_eq]
  have h := Matrix.exp_units_conj u (Matrix.diagonal (dv θ))
  simp only [u, Units.inv_mk] at h
  change NormedSpace.exp (P * Matrix.diagonal (dv θ) * Q) = _
  rw [show (P * Matrix.diagonal (dv θ) * Q) = (u : QQOp) * Matrix.diagonal (dv θ) * ((u⁻¹ : (QQOp)ˣ) : QQOp) from rfl,
    Matrix.exp_units_conj, Matrix.exp_diagonal]
  have e1 : NormedSpace.exp ((θ : ℂ) * Complex.I) = Real.cos θ + Real.sin θ * Complex.I := by
    rw [← Complex.exp_eq_exp_ℂ, Complex.exp_mul_I]; push_cast; ring
  have e2 : NormedSpace.exp (-((θ : ℂ) * Complex.I)) = Real.cos θ - Real.sin θ * Complex.I := by
    rw [← Complex.exp_eq_exp_ℂ, ← neg_mul, Complex.exp_mul_I]; push_cast
    rw [Complex.cos_neg, Complex.sin_neg]; ring
  have e0 : NormedSpace.exp (0 : ℂ) = 1 := NormedSpace.exp_zero
  ext ⟨a, b⟩ ⟨c, d⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [u, P, Q, dv, pairMatrix, pairIndex, Matrix.mul_apply, Fintype.sum_prod_type, adcUnitary,
      Matrix.diagonal_apply, Pi.coe_exp, e1, e2, e0] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring

end G56D

namespace G56D

lemma cos_pa (g : ℝ) (hg0 : 0 ≤ g) : Real.cos (principalAngle g) = Real.sqrt (1 - g) := by
  unfold principalAngle
  rw [Real.cos_arcsin, Real.sq_sqrt hg0]

lemma sin_pa (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) : Real.sin (principalAngle g) = Real.sqrt g := by
  unfold principalAngle
  rw [Real.sin_arcsin (by linarith [Real.sqrt_nonneg g]) (Real.sqrt_le_one.mpr hg1)]

lemma herm : adcDilationGenerator.IsHermitian := by
  ext ⟨a, b⟩ ⟨c, d⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [adcDilationGenerator, Matrix.kronecker, pauliX, pauliY] <;> ring

lemma unit (θ : ℝ) : adcUnitary θ ∈ Matrix.unitaryGroup (Bool × Bool) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  have h : Complex.cos (θ : ℂ) ^ 2 + Complex.sin (θ : ℂ) ^ 2 = 1 := Complex.cos_sq_add_sin_sq _
  have h' : Complex.sin (θ : ℂ) ^ 2 + Complex.cos (θ : ℂ) ^ 2 = 1 := by rw [add_comm]; exact h
  have hc : (starRingEnd ℂ) (Complex.cos (θ : ℂ)) = Complex.cos (θ : ℂ) := by
    rw [← Complex.ofReal_cos, Complex.conj_ofReal]
  have hs : (starRingEnd ℂ) (Complex.sin (θ : ℂ)) = Complex.sin (θ : ℂ) := by
    rw [← Complex.ofReal_sin, Complex.conj_ofReal]
  ext ⟨a, b⟩ ⟨c, d⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [adcUnitary, pairMatrix, pairIndex, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply,
      Complex.conj_ofReal, hc, hs] <;> ring_nf <;> (try simp [h, h'])

lemma cross_adc (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (rho : QOp) :
    cross (dilation g) (dilation g) false rho = adc g rho := by
  ext s t
  cases s <;> cases t <;>
    simp [cross, traceEnv, cleanInput, dilation, adcUnitary, adc, k0, k1, cos_pa g hg0, sin_pa g hg0 hg1,
      Matrix.mul_apply, pairMatrix, pairIndex, Fintype.sum_prod_type, Matrix.kronecker, Matrix.single_apply,
      Matrix.diagonal_apply, Complex.conj_ofReal] <;> ring

lemma chan (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) : IsChannel (adc g) := by
  refine ⟨2, ![k0 g, k1 g], ?_, fun rho => ?_⟩
  · have h1 : ((Real.sqrt (1 - g) : ℂ)) * (Real.sqrt (1 - g) : ℂ) = 1 - (g : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith)]; push_cast; ring
    have h2 : ((Real.sqrt g : ℂ)) * (Real.sqrt g : ℂ) = (g : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hg0]
    unfold IsKrausFamily
    ext a b
    cases a <;> cases b <;>
      simp [Fin.sum_univ_two, k0, k1, Matrix.mul_apply, Matrix.diagonal_apply, Complex.conj_ofReal, h1, h2]
  · simp [krausApply, adc, Fin.sum_univ_two]

end G56D

open G56D in
theorem solution (theta : ℝ) (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) :
    adcDilationGenerator.IsHermitian ∧
    NormedSpace.exp ((-Complex.I * (theta : ℂ)) • adcDilationGenerator) = adcUnitary theta ∧
    adcUnitary theta ∈ Matrix.unitaryGroup (Bool × Bool) ℂ ∧
    Real.sin (principalAngle g) ^ 2 = g ∧
    interference (dilation g) false = k0 g ∧
    (∀ rho : QOp, cross (dilation g) (dilation g) false rho = adc g rho) ∧
    IsChannel (adc g) := by
  refine ⟨herm, exp_eq theta, unit theta, ?_, ?_, cross_adc g hg0 hg1, chan g hg0 hg1⟩
  · rw [sin_pa g hg0 hg1, Real.sq_sqrt hg0]
  · ext s t
    cases s <;> cases t <;>
      simp [interference, dilation, adcUnitary, k0, cos_pa g hg0, pairMatrix, pairIndex]
