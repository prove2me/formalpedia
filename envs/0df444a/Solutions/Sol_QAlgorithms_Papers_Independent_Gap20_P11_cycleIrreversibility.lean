-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap20.P11.cycleIrreversibility
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T07:26:14.489989+00:00
-- url     : https://prove2.me/submissions/4724a946-3950-4dbd-a2db-f558fa701237

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P11
noncomputable section
open QAlgorithms QAlgorithms.Papers.Independent.Gap20.P11
open scoped Matrix ComplexConjugate
open QAlgorithms.Papers.Independent.Gap48.P20 (Copies)
open QAlgorithms.Papers.Independent.Information100.P67 (conditionalEntropy)
attribute [local instance] Classical.propDecidable Classical.decEq
lemma g79f_trace_cfc_eq {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (P : Matrix X X ℂ) (Q : Matrix Y Y ℂ) (hP : P.IsHermitian) (hQ : Q.IsHermitian)
    (f : ℝ → ℝ) (hf : f 0 = 0) (htr : ∀ k : ℕ, (P ^ (k + 1)).trace = (Q ^ (k + 1)).trace) :
    (cfc f P).trace = (cfc f Q).trace := by
  classical
  set S : Finset ℝ := (P.finite_real_spectrum.union Q.finite_real_spectrum).toFinset ∪ {0} with hS
  set p : Polynomial ℝ := Lagrange.interpolate S id f with hp
  have hev : ∀ x ∈ S, p.eval x = f x := by
    intro x hx
    have := Lagrange.eval_interpolate_at_node (s := S) (v := id) f (Set.injOn_id _) hx
    exact this
  have hPe : cfc f P = Polynomial.aeval P p := by
    rw [← cfc_polynomial p P hP.isSelfAdjoint]
    apply cfc_congr
    intro x hx
    exact (hev x (by simp [hS, hx])).symm
  have hQe : cfc f Q = Polynomial.aeval Q p := by
    rw [← cfc_polynomial p Q hQ.isSelfAdjoint]
    apply cfc_congr
    intro x hx
    exact (hev x (by simp [hS, hx])).symm
  have h0 : p.coeff 0 = 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero, hev 0 (by simp [hS]), hf]
  rw [hPe, hQe, Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range,
    Matrix.trace_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.trace_smul, Matrix.trace_smul]
  rcases i with _ | k
  · simp [h0]
  · rw [htr k]

lemma g79f_pow_succ_mul {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (M : Matrix X Y ℂ) (k : ℕ) : (M * Mᴴ) ^ (k + 1) = M * (Mᴴ * M) ^ k * Mᴴ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, pow_succ]
    simp only [Matrix.mul_assoc]

lemma g79f_trace_pow {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (M : Matrix X Y ℂ) (k : ℕ) :
    ((M * Mᴴ) ^ (k + 1)).trace = ((Mᵀ * (Mᵀ)ᴴ) ^ (k + 1)).trace := by
  have h1 : Mᵀ * (Mᵀ)ᴴ = (Mᴴ * M)ᵀ := by
    rw [Matrix.transpose_mul]; rfl
  rw [h1, ← Matrix.transpose_pow, Matrix.trace_transpose, g79f_pow_succ_mul, Matrix.mul_assoc,
    Matrix.trace_mul_comm, pow_succ, Matrix.mul_assoc]

lemma g79f_entropy_swap {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (M : Matrix X Y ℂ) : vnEntropy (M * Mᴴ) = vnEntropy (Mᵀ * (Mᵀ)ᴴ) := by
  unfold vnEntropy
  rw [g79f_trace_cfc_eq _ _ (Matrix.isHermitian_mul_conjTranspose_self M)
    (Matrix.isHermitian_mul_conjTranspose_self Mᵀ) _ (by simp) (g79f_trace_pow M)]

theorem solution {A B R : Type} [Fintype A] [Fintype B] [Fintype R]
    [Nonempty A] [Nonempty B] [Nonempty R]
    (psi : EuclideanSpace ℂ (R × (A × B))) (hpsi : IsState psi) :
    vnEntropy (traceRight (traceLeft (pureDensity psi))) +
      conditionalEntropy (traceLeft (pureDensity psi)) = referenceInformation psi := by
  let M : Matrix (A × B) R ℂ := Matrix.of fun ab r => psi (r, ab)
  let N : Matrix B (A × R) ℂ := Matrix.of fun b ar => psi (ar.2, (ar.1, b))
  have h1 : traceLeft (pureDensity psi) = M * Mᴴ := by
    ext x y
    simp [traceLeft, pureDensity, M, Matrix.mul_apply]
  have h2 : traceRight (pureDensity psi) = Mᵀ * (Mᵀ)ᴴ := by
    ext x y
    simp [traceRight, pureDensity, M, Matrix.mul_apply]
  have h3 : traceLeft (traceLeft (pureDensity psi)) = N * Nᴴ := by
    ext x y
    simp only [traceLeft, pureDensity, N, Matrix.mul_apply, Matrix.of_apply,
      Matrix.conjTranspose_apply, RCLike.star_def, Fintype.sum_prod_type]
  have h4 : marginalAR (pureDensity psi) = Nᵀ * (Nᵀ)ᴴ := by
    ext x y
    simp [marginalAR, pureDensity, N, Matrix.mul_apply]
  unfold referenceInformation conditionalEntropy
  rw [h3, h2, h4, g79f_entropy_swap N, h1, g79f_entropy_swap M]
  ring
