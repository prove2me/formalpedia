-- Prove2me | solution 1 for RobustLS.Tikhonov.optimum_min_norm_of_lam_eq_tau
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:00:31.427265+00:00
-- url     : https://prove2.me/submissions/f6ba713e-e4bb-4a88-973a-dbc9bc58fcc7

import Mathlib
import Definitions.Def_RobustLS_Tikhonov_Core

namespace RobustLS.Tikhonov

open Matrix

theorem aux_omn_stack_sq {m : ℕ} (x : Fin m → ℝ) :
    ∑ i, stackOne x i ^ 2 = ∑ i, x i ^ 2 + 1 := by
  rw [Fintype.sum_sum_type]
  simp [stackOne]

theorem aux_omn_eq_zero {n : ℕ} (v : Fin n → ℝ) (h : eucNorm v ≤ 0) : v = 0 := by
  unfold eucNorm at h
  have hs : ∑ i, v i ^ 2 = 0 := by
    have h0 : 0 ≤ ∑ i, v i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg (v i))
    have := Real.sqrt_eq_zero'.mp (le_antisymm h (Real.sqrt_nonneg _))
    linarith
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (v i))).mp hs
  funext i
  have hi := this i (Finset.mem_univ i)
  simpa using hi

end RobustLS.Tikhonov

open RobustLS.Tikhonov
open Matrix

theorem solution {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    (b : Fin n → ℝ) (x : Fin m → ℝ) (lam tau : ℝ) (hopt : IsSOCPOptimal A b x lam tau)
    (heq : lam = tau) :
    IsMinNormSolution A b x := by
  obtain ⟨⟨h1, h2⟩, hmin⟩ := hopt
  subst heq
  have hAx : A *ᵥ x = b := by
    have := aux_omn_eq_zero (A *ᵥ x - b) (by linarith)
    exact sub_eq_zero.mp this
  refine ⟨hAx, fun y hy => ?_⟩
  have hfeas : IsSOCPFeasible A b y (eucNorm (stackOne y)) (eucNorm (stackOne y)) := by
    refine ⟨?_, le_refl _⟩
    rw [hy, sub_self]
    simp [eucNorm]
  have hle := hmin y _ _ hfeas
  have hxy : eucNorm (stackOne x) ≤ eucNorm (stackOne y) := le_trans h2 hle
  unfold eucNorm at hxy ⊢
  rw [aux_omn_stack_sq, aux_omn_stack_sq] at hxy
  have hy0 : 0 ≤ ∑ i, y i ^ 2 + 1 := by
    have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => sq_nonneg (y i))
    linarith
  have := (Real.sqrt_le_sqrt_iff hy0).mp hxy
  exact Real.sqrt_le_sqrt (by linarith)
