-- Prove2me | solution 1 for ProcessingNetworks.LyapunovCriteria.fluid_model_solution_globally_lipschitz
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:06:55.263829+00:00
-- url     : https://prove2.me/submissions/71e6d15c-a937-4dd0-b1a6-de20c909cfef

import Mathlib
import Definitions.Def_ProcessingNetworks_LyapunovCriteria_LipschitzOn
import Definitions.Def_ProcessingNetworks_LyapunovCriteria_FluidEquationData

open ProcessingNetworks.LyapunovCriteria in
theorem solution : ¬ (∀ {I J K : ℕ} (dat : FluidEquationData I J K)
    (hA : ∀ k j, 0 ≤ dat.A k j) (hAcol : ∀ j, ∃ k, 0 < dat.A k j)
    (Dh : ℝ → Fin I → ℝ) (Fh Th : ℝ → Fin J → ℝ) (Zh : ℝ → Fin I → ℝ)
    (hsol : IsFluidModelSolution dat Dh Fh Th Zh),
    IsGloballyLipschitzOn Dh (Set.Ici (0 : ℝ)) ∧ IsGloballyLipschitzOn Fh (Set.Ici (0 : ℝ)) ∧
    IsGloballyLipschitzOn Th (Set.Ici (0 : ℝ)) ∧ IsGloballyLipschitzOn Zh (Set.Ici (0 : ℝ))) := by
  intro h
  let dat : FluidEquationData 0 1 1 :=
    { B := 0, Γ := 0, m := 0, A := fun _ _ => 1, b := fun _ => 1, lam := 0 }
  have hsol : IsFluidModelSolution dat (fun _ => 0) (fun t _ => t ^ 2) (fun _ => 0) (fun _ => 0) := by
    refine ⟨fun _ _ i => i.elim0, fun _ _ i => i.elim0, fun _ _ i => i.elim0, ?_, ⟨rfl, ?_⟩, ?_⟩
    · intro t _ j; simp [dat]
    · intro a b _; exact le_refl _
    · intro s t _ hst k; simp [dat]; linarith
  obtain ⟨-, ⟨K, hK⟩, -⟩ := h dat (fun _ _ => zero_le_one) (fun _ => ⟨0, zero_lt_one⟩)
    _ _ _ _ hsol
  have hx : ((K : ℝ) + 1) ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr (by positivity)
  have h0 : (0 : ℝ) ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr le_rfl
  have := hK.dist_le_mul _ hx _ h0
  have hc : dist (((K : ℝ) + 1) ^ 2) ((0 : ℝ) ^ 2) ≤
      dist (fun _ : Fin 1 => ((K : ℝ) + 1) ^ 2) (fun _ : Fin 1 => (0 : ℝ) ^ 2) :=
    dist_le_pi_dist (fun _ : Fin 1 => ((K : ℝ) + 1) ^ 2) (fun _ : Fin 1 => (0 : ℝ) ^ 2) 0
  have h2 := hc.trans this
  rw [Real.dist_eq, Real.dist_eq] at h2
  have hKn : (0 : ℝ) ≤ K := K.2
  have e1 : |((K : ℝ) + 1) ^ 2 - (0 : ℝ) ^ 2| = ((K : ℝ) + 1) ^ 2 := by
    rw [abs_of_nonneg] <;> simp; positivity
  have e2 : |((K : ℝ) + 1) - 0| = (K : ℝ) + 1 := by
    rw [sub_zero, abs_of_nonneg (by positivity)]
  rw [e1, e2] at h2
  nlinarith


