-- Prove2me | solution 1 for ProbabilityTheory.IsLevyMeasure.exists_atomFree_seq_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T09:56:05.266596+00:00
-- url     : https://prove2.me/submissions/157ed098-151d-4638-8b7d-26cf1a9f4a64

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Theorems.Thm_ProbabilityTheory_IsLevyMeasure_exists_atomFree_radius
import Mathlib.Topology.Algebra.Order.Field
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

theorem solution {ν : Measure ℝ} (hν : IsLevyMeasure ν)
    {c : ℝ} (hc : 0 < c) : ∃ δ : ℕ → ℝ,
      (∀ m, 0 < δ m) ∧ (∀ m, δ m < c) ∧
      (∀ m, ν {x | |x| = δ m} = 0) ∧ Tendsto δ atTop (𝓝 0) := by
  have hb : ∀ m : ℕ, (0 : ℝ) < min (c / 2) (1 / ((m : ℝ) + 1)) := fun m => by positivity
  choose δ hδ_mem hδ_null using fun m => IsLevyMeasure.exists_atomFree_radius hν le_rfl (hb m)
  refine ⟨δ, fun m => (hδ_mem m).1, fun m => ?_, hδ_null, ?_⟩
  · calc δ m ≤ min (c / 2) (1 / ((m : ℝ) + 1)) := (hδ_mem m).2
      _ ≤ c / 2 := min_le_left _ _
      _ < c := by linarith
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      tendsto_one_div_add_atTop_nhds_zero_nat (fun m => (hδ_mem m).1.le) (fun m => ?_)
    exact (hδ_mem m).2.trans (min_le_right _ _)
