-- Prove2me | solution 1 for SoficGroups.rankDropCount_integral_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:52.29415+00:00
-- url     : https://prove2.me/submissions/438b8543-705b-405b-93a5-12218bc88c2f

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_measurableSet_shifted_floor_drop
import Theorems.Thm_SoficGroups_integrable_rankDropIndicator

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution {ι : Type*} [Fintype ι]
    (u v : ι → ℝ) (H : ℝ) :
    (∫ r, rankDropCount u v H r
      ∂(MeasureTheory.volume.restrict (Set.Ico 0 H))) =
      ∑ i : ι, (MeasureTheory.volume.restrict (Set.Ico 0 H)).real
        {r : ℝ | ⌊(v i + r) / H⌋ < ⌊(u i + r) / H⌋} := by
  classical
  unfold rankDropCount
  rw [MeasureTheory.integral_finsetSum Finset.univ
    (fun i hi => integrable_rankDropIndicator (u i) (v i) H)]
  apply Finset.sum_congr rfl
  intro i hi
  have hindicator :
      (fun r : ℝ =>
        if ⌊(v i + r) / H⌋ < ⌊(u i + r) / H⌋
          then (1 : ℝ) else 0) =
        {r : ℝ | ⌊(v i + r) / H⌋ < ⌊(u i + r) / H⌋}.indicator
          (fun _ : ℝ => (1 : ℝ)) := by
    funext r
    simp [Set.indicator]
  rw [hindicator]
  exact MeasureTheory.integral_indicator_one
    (measurableSet_shifted_floor_drop (u i) (v i) H)
end SoficGroups
