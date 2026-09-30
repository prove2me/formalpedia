-- Prove2me | solution 1 for UnderstandingML.soft_svm_slack_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-25T18:11:40.327834+00:00
-- url     : https://prove2.me/submissions/a6ceb42e-4574-42af-bad0-d9dbfa397be8

import Definitions.Def_UnderstandingML_SVM

open MeasureTheory
open scoped InnerProductSpace
open UnderstandingML

theorem solution {d m : ℕ} (x : Fin m → Vec d) (y : Fin m → ℝ) :
    (∀ (w : Vec d) (b : ℝ) (ξ : Fin m → ℝ), SoftSVMFeasible x y w b ξ →
      (∑ i, hingeLossAffine w b (x i, y i)) / m ≤ (∑ i, ξ i) / m) ∧
    ∀ (w : Vec d) (b : ℝ),
      SoftSVMFeasible x y w b (fun i ↦ hingeLossAffine w b (x i, y i)) := by
  refine ⟨fun w b ξ h => ?_, fun w b i => ?_⟩
  · apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg m)
    apply Finset.sum_le_sum
    intro i _
    obtain ⟨h1, h2⟩ := h i
    simp only [hingeLossAffine]
    exact max_le h2 (by linarith)
  · simp only [hingeLossAffine]
    exact ⟨by linarith [le_max_right 0 (1 - y i * (⟪w, x i⟫_ℝ + b))], le_max_left _ _⟩
