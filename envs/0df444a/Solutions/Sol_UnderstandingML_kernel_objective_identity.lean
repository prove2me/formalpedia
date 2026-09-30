-- Prove2me | solution 1 for UnderstandingML.kernel_objective_identity
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-25T18:53:26.049472+00:00
-- url     : https://prove2.me/submissions/d8c33039-4335-4157-b69f-e191d0d2e4a4

import Definitions.Def_UnderstandingML_Kernel

open MeasureTheory
open scoped InnerProductSpace

universe u

open UnderstandingML

theorem solution {X : Type u} {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace F] {m : ℕ} (ψ : X → F) (x : Fin m → X)
    (f : (Fin m → ℝ) → ℝ) (R : ℝ → ℝ) (α : Fin m → ℝ) :
    kernelObjective ψ x f R (∑ j, α j • ψ (x j)) =
      f (fun i ↦ ∑ j, α j * kernelOf ψ (x j) (x i)) +
        R (Real.sqrt (∑ i, ∑ j, α i * α j * kernelOf ψ (x j) (x i))) := by
  unfold kernelObjective kernelOf
  have hinner : ∀ i, ⟪∑ j, α j • ψ (x j), ψ (x i)⟫_ℝ = ∑ j, α j * ⟪ψ (x j), ψ (x i)⟫_ℝ := by
    intro i
    rw [sum_inner]
    simp [real_inner_smul_left]
  have hnorm : ‖∑ j, α j • ψ (x j)‖ =
      Real.sqrt (∑ i, ∑ j, α i * α j * ⟪ψ (x j), ψ (x i)⟫_ℝ) := by
    rw [← Real.sqrt_sq (norm_nonneg _), ← real_inner_self_eq_norm_sq]
    congr 1
    rw [inner_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_smul_right, hinner, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hnorm]
  congr 2
  funext i
  exact hinner i
