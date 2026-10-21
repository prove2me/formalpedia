-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P34.pure_tripartite_entropy_balances
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T23:58:45.698425+00:00
-- url     : https://prove2.me/submissions/0e057226-c7ec-40b0-8244-fc030aaf03ac

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P34
noncomputable section

open scoped Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Renew46 QAlgorithms.Papers.Independent.Renew46.P34

lemma g64g_trace_cfc_eq {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
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

lemma g64g_pow_succ_mul {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (M : Matrix X Y ℂ) (k : ℕ) : (M * Mᴴ) ^ (k + 1) = M * (Mᴴ * M) ^ k * Mᴴ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, pow_succ]
    simp only [Matrix.mul_assoc]

lemma g64g_trace_pow {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (M : Matrix X Y ℂ) (k : ℕ) :
    ((M * Mᴴ) ^ (k + 1)).trace = ((Mᵀ * (Mᵀ)ᴴ) ^ (k + 1)).trace := by
  have h1 : Mᵀ * (Mᵀ)ᴴ = (Mᴴ * M)ᵀ := by
    rw [Matrix.transpose_mul]; rfl
  rw [h1, ← Matrix.transpose_pow, Matrix.trace_transpose, g64g_pow_succ_mul, Matrix.mul_assoc,
    Matrix.trace_mul_comm, pow_succ, Matrix.mul_assoc]

lemma g64g_entropy_swap {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (M : Matrix X Y ℂ) : vnEntropy (M * Mᴴ) = vnEntropy (Mᵀ * (Mᵀ)ᴴ) := by
  unfold vnEntropy
  rw [g64g_trace_cfc_eq _ _ (Matrix.isHermitian_mul_conjTranspose_self M)
    (Matrix.isHermitian_mul_conjTranspose_self Mᵀ) _ (by simp) (g64g_trace_pow M)]

lemma g64g_ab_e {A B E : Type} [Fintype A] [Fintype B] [Fintype E]
    (psi : EuclideanSpace ℂ ((A × B) × E)) :
    vnEntropy (traceRight (pureDensity psi)) = vnEntropy (traceLeft (pureDensity psi)) := by
  set M : Matrix (A × B) E ℂ := Matrix.of fun i e => psi (i, e)
  have h1 : traceRight (pureDensity psi) = M * Mᴴ := by
    ext i j; simp [traceRight, pureDensity, M, Matrix.mul_apply]
  have h2 : traceLeft (pureDensity psi) = Mᵀ * (Mᵀ)ᴴ := by
    ext i j; simp [traceLeft, pureDensity, M, Matrix.mul_apply]
  rw [h1, h2]; exact g64g_entropy_swap M

lemma g64g_ae_b {A B E : Type} [Fintype A] [Fintype B] [Fintype E]
    (psi : EuclideanSpace ℂ ((A × B) × E)) :
    vnEntropy (fun i j : A × E => ∑ b, pureDensity psi ((i.1,b),i.2) ((j.1,b),j.2)) =
      vnEntropy (traceLeft (traceRight (pureDensity psi))) := by
  set M : Matrix (A × E) B ℂ := Matrix.of fun i b => psi ((i.1, b), i.2)
  have h1 : (fun i j : A × E => ∑ b, pureDensity psi ((i.1,b),i.2) ((j.1,b),j.2)) = M * Mᴴ := by
    ext i j; simp [pureDensity, M, Matrix.mul_apply]
  have h2 : traceLeft (traceRight (pureDensity psi)) = Mᵀ * (Mᵀ)ᴴ := by
    ext i j; simp [traceLeft, traceRight, pureDensity, M, Matrix.mul_apply, Fintype.sum_prod_type]
  rw [h1, h2]; exact g64g_entropy_swap M

theorem solution {A B E : Type}
    [Fintype A] [Fintype B] [Fintype E] [Nonempty A] [Nonempty B] [Nonempty E]
    (psi : EuclideanSpace ℂ ((A × B) × E)) (hpsi : IsState psi) :
    vnEntropy (sourceAB psi) = vnEntropy (traceLeft (pureDensity psi)) ∧
    vnEntropy (sourceAE psi) = vnEntropy (traceLeft (sourceAB psi)) ∧
    informationAB psi / 2 + informationAE psi / 2 = entropyA psi ∧
    informationAB psi / 2 - informationAE psi / 2 = (vnEntropy (traceLeft (sourceAB psi)) - vnEntropy (sourceAB psi)) := by
  have h1 : vnEntropy (sourceAB psi) = vnEntropy (traceLeft (pureDensity psi)) := g64g_ab_e psi
  have h2 : vnEntropy (sourceAE psi) = vnEntropy (traceLeft (sourceAB psi)) := g64g_ae_b psi
  refine ⟨h1, h2, ?_, ?_⟩
  · simp only [informationAB, informationAE]; rw [h1, h2]; ring
  · simp only [informationAB, informationAE]; rw [h1, h2]; ring
