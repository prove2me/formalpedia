-- Prove2me | solution 1 for RobustMultitask.Estimator.eq_6_well_aligned_card
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T14:50:04.658002+00:00
-- url     : https://prove2.me/submissions/952dbcf9-ef1e-42f1-a76c-255e18b88b0e

import Mathlib
import Definitions.Def_RobustMultitask_Estimator_VectorNotation
import Definitions.Def_RobustMultitask_Estimator_Alignment

open RobustMultitask.Estimator in
theorem solution {N d : ℕ} (β : Fin N → Fin d → ℝ) (βdag : Fin d → ℝ) (s : ℕ)
    (ζ : ℝ) (hζ : 0 < ζ) (hsparse : ∀ j, l0 (β j - βdag) ≤ s) :
    ((wellAligned β βdag ζ).card : ℝ) ≤ (s : ℝ) / ζ := by
  have hmem : ∀ i, i ∈ wellAligned β βdag ζ ↔ ζ ≤ ((misalignedTasks β βdag i).card : ℝ) / N := by
    intro i
    simp [wellAligned, poorlyAligned]
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have : wellAligned β βdag ζ = ∅ := by
      ext i
      rw [hmem]
      simp only [Nat.cast_zero, div_zero, Finset.notMem_empty, iff_false, not_le]
      exact hζ
    rw [this, Finset.card_empty, Nat.cast_zero]
    positivity
  · have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    -- double counting
    have hdc : ∑ i, (misalignedTasks β βdag i).card = ∑ j, l0 (β j - βdag) := by
      simp only [misalignedTasks, l0, Finset.card_filter, Pi.sub_apply, sub_ne_zero]
      exact Finset.sum_comm
    have hbound : ∑ i, (misalignedTasks β βdag i).card ≤ N * s := by
      rw [hdc]
      calc ∑ j, l0 (β j - βdag) ≤ ∑ _j : Fin N, s := Finset.sum_le_sum fun j _ => hsparse j
        _ = N * s := by simp
    have hsub : ∑ i ∈ wellAligned β βdag ζ, (misalignedTasks β βdag i).card ≤ N * s :=
      le_trans (Finset.sum_le_sum_of_subset (Finset.subset_univ _)) hbound
    have hsubR : (∑ i ∈ wellAligned β βdag ζ, ((misalignedTasks β βdag i).card : ℝ)) ≤ N * s := by
      exact_mod_cast hsub
    have hlow : ∑ i ∈ wellAligned β βdag ζ, ζ * N ≤
        ∑ i ∈ wellAligned β βdag ζ, ((misalignedTasks β βdag i).card : ℝ) := by
      refine Finset.sum_le_sum fun i hi => ?_
      have := (hmem i).mp hi
      rwa [le_div_iff₀ hNR] at this
    rw [Finset.sum_const, nsmul_eq_mul] at hlow
    rw [le_div_iff₀ hζ]
    have : ((wellAligned β βdag ζ).card : ℝ) * ζ * N ≤ s * N := by nlinarith
    nlinarith
