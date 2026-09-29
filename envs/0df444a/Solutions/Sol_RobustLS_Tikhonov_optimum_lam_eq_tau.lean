-- Prove2me | solution 1 for RobustLS.Tikhonov.optimum_lam_eq_tau
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T22:54:35.076858+00:00
-- url     : https://prove2.me/submissions/039525a1-8cd9-4a8e-bf6b-d2bda6763fa2

import Mathlib
import Definitions.Def_RobustLS_Tikhonov_Core

namespace RobustLS.Tikhonov

open Matrix

theorem aux_olt_stack_norm {m : ℕ} (x : Fin m → ℝ) :
    eucNorm (stackOne x) = Real.sqrt (eucNorm x ^ 2 + 1) := by
  unfold eucNorm stackOne
  rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg (x i)))]
  congr 1
  rw [Fintype.sum_sum_type]
  simp

theorem aux_olt_eq_of_norm_le_zero {n : ℕ} (v : Fin n → ℝ) (h : eucNorm v ≤ 0) : v = 0 := by
  unfold eucNorm at h
  have hs : ∑ i, v i ^ 2 ≤ 0 := by
    have h0 : Real.sqrt (∑ i, v i ^ 2) = 0 := le_antisymm h (Real.sqrt_nonneg _)
    exact (Real.sqrt_eq_zero').mp h0
  have hs0 : ∑ i, v i ^ 2 = 0 :=
    le_antisymm hs (Finset.sum_nonneg (fun i _ => sq_nonneg (v i)))
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (v i))] at hs0
  funext i
  have := hs0 i (Finset.mem_univ i)
  simpa using this

end RobustLS.Tikhonov

open RobustLS.Tikhonov
open Matrix

theorem solution {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin n → ℝ)
    (x : Fin m → ℝ) (lam tau : ℝ) (hopt : IsSOCPOptimal A b x lam tau) (heq : lam = tau) :
    A *ᵥ x = b ∧ lam = Real.sqrt (eucNorm x ^ 2 + 1) ∧ tau = Real.sqrt (eucNorm x ^ 2 + 1) := by
  obtain ⟨⟨h1, h2⟩, hmin⟩ := hopt
  have hAx : A *ᵥ x - b = 0 := by
    apply aux_olt_eq_of_norm_le_zero
    rw [heq, sub_self] at h1
    exact h1
  have hAxb : A *ᵥ x = b := sub_eq_zero.mp hAx
  set s := eucNorm (stackOne x) with hs
  have hfeas : IsSOCPFeasible A b x s s := by
    refine ⟨?_, le_refl _⟩
    rw [hAx, sub_self]
    unfold eucNorm
    simp
  have hle : lam ≤ s := hmin x s s hfeas
  have hlam : lam = s := le_antisymm hle (heq ▸ h2)
  rw [hs, aux_olt_stack_norm] at hlam
  exact ⟨hAxb, hlam, heq ▸ hlam⟩
