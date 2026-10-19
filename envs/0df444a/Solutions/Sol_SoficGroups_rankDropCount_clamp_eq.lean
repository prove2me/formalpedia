-- Prove2me | solution 1 for SoficGroups.rankDropCount_clamp_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:52.29415+00:00
-- url     : https://prove2.me/submissions/061c24f3-994c-4f3f-80f1-9373cd7b3a87

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution {ι : Type*} [Fintype ι]
    (u v : ι → ℝ) (H r : ℝ) (hH : 0 < H) :
    rankDropCount u v H r =
      rankDropCount u (fun i => min (v i) (u i)) H r := by
  classical
  unfold rankDropCount
  apply Finset.sum_congr rfl
  intro i hi
  change
    (if ⌊(v i + r) / H⌋ < ⌊(u i + r) / H⌋
      then (1 : ℝ) else 0) =
      if ⌊(min (v i) (u i) + r) / H⌋ < ⌊(u i + r) / H⌋
        then (1 : ℝ) else 0
  by_cases hle : v i ≤ u i
  · rw [min_eq_left hle]
  · have hreverse : u i ≤ v i := le_of_not_ge hle
    have hfloor :
        ¬ ⌊(v i + r) / H⌋ < ⌊(u i + r) / H⌋ := by
      apply not_lt_of_ge
      apply Int.floor_mono
      apply (div_le_div_iff_of_pos_right hH).2
      linarith
    simp [min_eq_right hreverse, hfloor]
end SoficGroups
