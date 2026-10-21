-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P40.pure_conditional_entropy_duality
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T17:20:38.847409+00:00
-- url     : https://prove2.me/submissions/541f3e27-f737-4538-90a1-61fb66fae157

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P40
noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Next46 QAlgorithms.Papers.Independent.Next46.P40

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P19 (mutualInformation marginalRB associate)

variable {A B C E R S : Type*}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype E] [Fintype R] [Fintype S]

variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq E]

variable [DecidableEq R] [DecidableEq S]

lemma g62j_trace_cfc_eq {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
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

lemma g62j_pow_succ_mul {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (M : Matrix X Y ℂ) (k : ℕ) : (M * Mᴴ) ^ (k + 1) = M * (Mᴴ * M) ^ k * Mᴴ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, pow_succ]
    simp only [Matrix.mul_assoc]

lemma g62j_trace_pow {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (M : Matrix X Y ℂ) (k : ℕ) :
    ((M * Mᴴ) ^ (k + 1)).trace = ((Mᵀ * (Mᵀ)ᴴ) ^ (k + 1)).trace := by
  have h1 : Mᵀ * (Mᵀ)ᴴ = (Mᴴ * M)ᵀ := by
    rw [Matrix.transpose_mul]; rfl
  rw [h1, ← Matrix.transpose_pow, Matrix.trace_transpose, g62j_pow_succ_mul, Matrix.mul_assoc,
    Matrix.trace_mul_comm, pow_succ, Matrix.mul_assoc]

lemma g62j_entropy_swap {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (M : Matrix X Y ℂ) : vnEntropy (M * Mᴴ) = vnEntropy (Mᵀ * (Mᵀ)ᴴ) := by
  unfold vnEntropy
  rw [g62j_trace_cfc_eq _ _ (Matrix.isHermitian_mul_conjTranspose_self M)
    (Matrix.isHermitian_mul_conjTranspose_self Mᵀ) _ (by simp) (g62j_trace_pow M)]

/-- PDF p.4, Lemma 3: pure-state conditional-entropy duality.
All density matrices in the formula are computed from the normalized vector. -/
theorem solution
    [Nonempty A] [Nonempty B] [Nonempty E]
    (v : EuclideanSpace ℂ ((A × B) × E)) (hv : ‖v‖ = 1) :
    vnEntropy (marginalBC (pureDensity v)) - vnEntropy (traceLeft (pureDensity v)) =
      -(vnEntropy (traceRight (pureDensity v)) -
        vnEntropy (traceRight (traceRight (pureDensity v)))) := by
  have e1 : traceRight (pureDensity v) = (Matrix.of fun ab e => v (ab, e)) *
      (Matrix.of fun ab e => v (ab, e))ᴴ := by
    ext i j; simp [traceRight, pureDensity, Matrix.mul_apply, Matrix.conjTranspose_apply]
  have e2 : traceLeft (pureDensity v) = (Matrix.of fun ab e => v (ab, e))ᵀ *
      ((Matrix.of fun ab e => v (ab, e))ᵀ)ᴴ := by
    ext i j; simp [traceLeft, pureDensity, Matrix.mul_apply, Matrix.conjTranspose_apply]
  have e3 : traceRight (traceRight (pureDensity v)) =
      (Matrix.of fun (a : A) (be : B × E) => v ((a, be.1), be.2)) *
      (Matrix.of fun (a : A) (be : B × E) => v ((a, be.1), be.2))ᴴ := by
    ext i j; simp [traceRight, pureDensity, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type]
  have e4 : marginalBC (pureDensity v) =
      (Matrix.of fun (a : A) (be : B × E) => v ((a, be.1), be.2))ᵀ *
      ((Matrix.of fun (a : A) (be : B × E) => v ((a, be.1), be.2))ᵀ)ᴴ := by
    ext i j; simp [marginalBC, pureDensity, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [e3, e4, e1, e2, ← g62j_entropy_swap, ← g62j_entropy_swap]
  ring



end
