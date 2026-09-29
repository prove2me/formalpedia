-- Prove2me | solution 1 for SDYM.classical_darboux_halphen_of_chazy_roots
-- status  : ACCEPTED   (disprove)
-- author  : @cm_beta
-- created : 2026-09-23T22:18:43.291617+00:00
-- url     : https://prove2.me/submissions/deab57a6-9f46-4cea-829f-6f6dcd636af1

import Definitions.Def_SDYM_ChazyEquations
import Definitions.Def_SDYM_DarbouxHalphenRamanujan

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

open SDYM

theorem solution : ¬ (∀ (s : Set ℂ) (y y₁ y₂ w₁ w₂ w₃ : ℂ → ℂ)
    (hy : IsChazySolution s y y₁ y₂)
    (hw₁ : ∀ t ∈ s, DifferentiableAt ℂ w₁ t)
    (hw₂ : ∀ t ∈ s, DifferentiableAt ℂ w₂ t)
    (hw₃ : ∀ t ∈ s, DifferentiableAt ℂ w₃ t)
    (hroots : ∀ t ∈ s, ∀ z : ℂ,
      z ^ 3 + y t / 2 * z ^ 2 + y₁ t / 2 * z + y₂ t / 12
        = (z - w₁ t) * (z - w₂ t) * (z - w₃ t))
    (hdist : ∀ t ∈ s, w₁ t ≠ w₂ t ∧ w₂ t ≠ w₃ t ∧ w₃ t ≠ w₁ t),
    IsClassicalDHSolution s w₁ w₂ w₃) := by
  intro H
  have lin : ∀ u v : ℂ, HasDerivAt (fun t : ℂ => u + v * t) v 0 := fun u v =>
    (((hasDerivAt_id' (0 : ℂ)).const_mul v).const_add u).congr_deriv (by ring)
  have := H {0} (fun t => -12 + 22 * t) (fun t => 22 + (-72) * t) (fun t => -72 + 276 * t)
    (fun t => 1 + 100 * t) (fun _ => 2) (fun _ => 3)
    (by
      unfold IsChazySolution
      refine ⟨?_, ?_, ?_⟩
      · intro t ht
        rw [Set.mem_singleton_iff] at ht
        subst ht
        exact (lin _ _).congr_deriv (by norm_num)
      · intro t ht
        rw [Set.mem_singleton_iff] at ht
        subst ht
        exact (lin _ _).congr_deriv (by norm_num)
      · intro t ht
        rw [Set.mem_singleton_iff] at ht
        subst ht
        exact (lin _ _).congr_deriv (by norm_num))
    (fun t _ => (((hasDerivAt_id' t).const_mul (100 : ℂ)).const_add 1).differentiableAt)
    (fun t _ => differentiableAt_const _)
    (fun t _ => differentiableAt_const _)
    (by
      intro t ht z
      rw [Set.mem_singleton_iff] at ht
      subst ht
      (try beta_reduce)
      ring)
    (by
      intro t ht
      rw [Set.mem_singleton_iff] at ht
      subst ht
      norm_num)
  obtain ⟨h1', -, -⟩ := this
  have h1 := h1' 0 (Set.mem_singleton 0)
  have h2 := lin 1 100
  have := h1.unique h2
  norm_num at this
