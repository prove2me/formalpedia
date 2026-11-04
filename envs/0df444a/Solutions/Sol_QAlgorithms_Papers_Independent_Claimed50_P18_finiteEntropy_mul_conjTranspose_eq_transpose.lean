-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P18.finiteEntropy_mul_conjTranspose_eq_transpose
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-03T23:47:26.470417+00:00
-- url     : https://prove2.me/submissions/f3cb9e75-6a62-4ada-9953-58975481ff4b

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P18

noncomputable section

open Filter

open scoped ENNReal BigOperators

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

open QAlgorithms.Papers.Independent.Frontier18.P01

open QAlgorithms.Papers.Independent.Frontier18.P08 (operatorTrace)

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Claimed50.P18

open scoped Matrix ComplexOrder

/-- `(W V)^(k+1) = W (V W)^k V`. -/
theorem fecc_pow {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (W : Matrix m n ℂ) (V : Matrix n m ℂ) (k : ℕ) :
    (W * V) ^ (k + 1) = W * (V * W) ^ k * V := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, pow_succ]
    simp only [Matrix.mul_assoc]

/-- `tr (W V)^(k+1) = tr (V W)^(k+1)`. -/
theorem fecc_trace_pow {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (W : Matrix m n ℂ) (V : Matrix n m ℂ) (k : ℕ) :
    ((W * V) ^ (k + 1)).trace = ((V * W) ^ (k + 1)).trace := by
  rw [fecc_pow, Matrix.trace_mul_comm, ← Matrix.mul_assoc, pow_succ']

/-- If two self-adjoint matrices have equal traces of all positive powers, then
`tr f(A) = tr f(B)` for every `f` with `f 0 = 0` (polynomial interpolation on the spectra). -/
theorem fecc_trace_cfc {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m m ℂ) (B : Matrix n n ℂ) (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (h : ∀ k : ℕ, (A ^ (k + 1)).trace = (B ^ (k + 1)).trace) (f : ℝ → ℝ) (hf : f 0 = 0) :
    (cfc f A).trace = (cfc f B).trace := by
  set s : Finset ℝ := (Matrix.finite_real_spectrum (A := A)).toFinset ∪
    (Matrix.finite_real_spectrum (A := B)).toFinset ∪ {0} with hs
  set p : Polynomial ℝ := Lagrange.interpolate s id f with hp
  have hev : ∀ x ∈ s, p.eval x = f x := fun x hx =>
    Lagrange.eval_interpolate_at_node (v := id) f (Set.injOn_id _) hx
  have hA' : cfc f A = Polynomial.aeval A p := by
    rw [← cfc_polynomial p A]
    exact cfc_congr (fun x hx => (hev x (by simp [hs, hx])).symm)
  have hB' : cfc f B = Polynomial.aeval B p := by
    rw [← cfc_polynomial p B]
    exact cfc_congr (fun x hx => (hev x (by simp [hs, hx])).symm)
  have key : ∀ (C : Type) [Fintype C] [DecidableEq C] (M : Matrix C C ℂ),
      (Polynomial.aeval M p).trace =
        ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i • (M ^ i).trace := by
    intro C _ _ M
    rw [Polynomial.aeval_eq_sum_range, Matrix.trace_sum]
    simp [Matrix.trace_smul]
  rw [hA', hB', key, key]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases i with _ | k
  · have h0 : p.coeff 0 = 0 := by
      rw [Polynomial.coeff_zero_eq_eval_zero, hev 0 (by simp [hs]), hf]
    simp [h0]
  · rw [h k]

theorem fecc_main {m n : Type} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (W : Matrix m n ℂ) :
    finiteEntropy (W * Wᴴ) = finiteEntropy (Wᵀ * Wᵀᴴ) := by
  have hT : Wᵀ * Wᵀᴴ = (Wᴴ * W)ᵀ := by
    rw [Matrix.transpose_mul]; rfl
  have hpow : ∀ k : ℕ, ((W * Wᴴ) ^ (k + 1)).trace = ((Wᵀ * Wᵀᴴ) ^ (k + 1)).trace := by
    intro k
    rw [hT, ← Matrix.transpose_pow, Matrix.trace_transpose, fecc_trace_pow]
  have hsa1 : IsSelfAdjoint (W * Wᴴ) := Matrix.isHermitian_mul_conjTranspose_self W
  have hsa2 : IsSelfAdjoint (Wᵀ * Wᵀᴴ) := Matrix.isHermitian_mul_conjTranspose_self Wᵀ
  have h1 := hpow 0
  simp only [zero_add, pow_one] at h1
  unfold finiteEntropy
  rw [fecc_trace_cfc _ _ hsa1 hsa2 hpow _ (by simp), h1]

end QAlgorithms.Papers.Independent.Claimed50.P18

end

open QAlgorithms.Papers.Independent.Claimed50.P18 in
open scoped Matrix in
open QAlgorithms.Papers.Independent.Frontier18.P01 in
theorem solution {m n : Type} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (W : Matrix m n ℂ) :
    finiteEntropy (W * Wᴴ) = finiteEntropy (Wᵀ * Wᵀᴴ) :=
  fecc_main W
