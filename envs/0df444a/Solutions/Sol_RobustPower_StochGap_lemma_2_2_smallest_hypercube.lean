-- Prove2me | solution 1 for RobustPower.StochGap.lemma_2_2_smallest_hypercube
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T01:59:46.332747+00:00
-- url     : https://prove2.me/submissions/a7545b5a-cd65-4d13-b8fc-8cd45e55b8a4

import Mathlib
import Definitions.Def_RobustPower_StochGap_SymmetricSets

open RobustPower.StochGap in
theorem solution {n : ℕ} (S : Set (Fin n → ℝ))
    (hS : IsSymmetric S) (hbdd : Bornology.IsBounded S) :
    IsHypercube (boundingBox S) ∧ S ⊆ boundingBox S ∧
      ∀ H' : Set (Fin n → ℝ), IsHypercube H' → S ⊆ H' → boundingBox S ⊆ H' := by
  obtain ⟨u, hu, -⟩ := hS
  obtain ⟨r, hr⟩ := hbdd.subset_closedBall 0
  have hle : ∀ x ∈ S, ∀ j, |x j| ≤ r := by
    intro x hx j
    have h1 := hr hx
    rw [Metric.mem_closedBall, dist_zero_right] at h1
    have h2 : ‖x j‖ ≤ ‖x‖ := norm_le_pi_norm x j
    rw [Real.norm_eq_abs] at h2
    linarith
  have hne : ∀ j, ((fun x : Fin n → ℝ => x j) '' S).Nonempty := fun j => ⟨u j, u, hu, rfl⟩
  have hba : ∀ j, BddAbove ((fun x : Fin n → ℝ => x j) '' S) := by
    intro j
    refine ⟨r, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact (abs_le.mp (hle x hx j)).2
  have hbb : ∀ j, BddBelow ((fun x : Fin n → ℝ => x j) '' S) := by
    intro j
    refine ⟨-r, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact (abs_le.mp (hle x hx j)).1
  have hsub : S ⊆ boundingBox S := by
    intro x hx
    refine ⟨fun j => ?_, fun j => ?_⟩
    · exact csInf_le (hbb j) ⟨x, hx, rfl⟩
    · exact le_csSup (hba j) ⟨x, hx, rfl⟩
  refine ⟨⟨xl S, xh S, ?_, rfl⟩, hsub, ?_⟩
  · intro j
    exact le_trans ((hsub hu).1 j) ((hsub hu).2 j)
  · rintro H' ⟨l, v, -, rfl⟩ hSH
    apply Set.Icc_subset_Icc
    · intro j
      apply le_csInf (hne j)
      rintro _ ⟨x, hx, rfl⟩
      exact (hSH hx).1 j
    · intro j
      apply csSup_le (hne j)
      rintro _ ⟨x, hx, rfl⟩
      exact (hSH hx).2 j
