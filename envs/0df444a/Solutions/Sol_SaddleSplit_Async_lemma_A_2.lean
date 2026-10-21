-- Prove2me | solution 1 for SaddleSplit.Async.lemma_A_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T16:12:33.360093+00:00
-- url     : https://prove2.me/submissions/003eb1c1-d357-4d4e-b655-88b1151328c3

import Mathlib
import Definitions.Def_SaddleSplit_Async_Setting

open InnerProductSpace Filter Topology
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR
open SaddleSplit.Async

theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (α : ℝ) (hα : 0 ≤ α) (A : E → E) (hA : ∀ x y, ‖A x - A y‖ ≤ α * ‖x - y‖)
    (σ : ℝ) (hσ : 0 < σ) (γ : ℝ) (hγ : γ ∈ Set.Ioc 0 (1 / (α + σ))) :
    IsStronglyMonotone σ (fun x => γ⁻¹ • x - A x) := by
  intro x y
  obtain ⟨hγ0, hγ1⟩ := hγ
  have hpos : 0 < α + σ := by linarith
  have hinv : α + σ ≤ γ⁻¹ := by
    rw [le_inv_comm₀ hpos hγ0]; simpa [one_div] using hγ1
  have e : (γ⁻¹ • x - A x) - (γ⁻¹ • y - A y) = γ⁻¹ • (x - y) - (A x - A y) := by
    rw [smul_sub]; abel
  simp only
  rw [e, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
  have cs : ⟪x - y, A x - A y⟫_ℝ ≤ ‖x - y‖ * ‖A x - A y‖ := real_inner_le_norm _ _
  have h2 : ‖x - y‖ * ‖A x - A y‖ ≤ ‖x - y‖ * (α * ‖x - y‖) :=
    mul_le_mul_of_nonneg_left (hA x y) (norm_nonneg _)
  have h3 : (α + σ) * ‖x - y‖ ^ 2 ≤ γ⁻¹ * ‖x - y‖ ^ 2 :=
    mul_le_mul_of_nonneg_right hinv (sq_nonneg _)
  nlinarith
