-- Prove2me | solution 1 for ProbabilityTheory.IsLevyMeasure.exists_atomFree_radius
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T09:48:43.583777+00:00
-- url     : https://prove2.me/submissions/2a3fda31-7b90-47fd-ac3f-dda92063b35f

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Theorems.Thm_ProbabilityTheory_exists_atomFree_radius
import Theorems.Thm_ProbabilityTheory_IsLevyMeasure_isFiniteMeasure_restrict_largeSet
import Mathlib.MeasureTheory.Measure.MeasureSpace
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

theorem solution {ν : Measure ℝ} (hν : IsLevyMeasure ν) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) :
    ∃ r ∈ Set.Ioc a b, ν {x | |x| = r} = 0 := by
  have hb_pos : 0 < b := ha.trans_lt hab
  have hc₀_pos : 0 < max a (b / 2) := lt_of_lt_of_le (by linarith) (le_max_right a (b / 2))
  have hc₀_lt_b : max a (b / 2) < b := max_lt hab (by linarith)
  have hc₀_ge_a : a ≤ max a (b / 2) := le_max_left a (b / 2)
  haveI : IsFiniteMeasure (ν.restrict (largeSet (max a (b / 2) / 2))) :=
    IsLevyMeasure.isFiniteMeasure_restrict_largeSet hν (by linarith)
  obtain ⟨r, hr_mem, hr_null⟩ :=
    ProbabilityTheory.exists_atomFree_radius (ν.restrict (largeSet (max a (b / 2) / 2))) hc₀_lt_b
  have hsub : {x : ℝ | |x| = r} ⊆ largeSet (max a (b / 2) / 2) := fun x hx => by
    simp only [Set.mem_setOf_eq] at hx
    change max a (b / 2) / 2 ≤ |x|
    rw [hx]
    linarith [hr_mem.1]
  have hmeas : MeasurableSet (largeSet (max a (b / 2) / 2)) :=
    (isClosed_Ici.preimage continuous_abs).measurableSet
  rw [Measure.restrict_apply' hmeas,
    Set.inter_eq_self_of_subset_left hsub] at hr_null
  exact ⟨r, ⟨hc₀_ge_a.trans_lt hr_mem.1, hr_mem.2⟩, hr_null⟩
