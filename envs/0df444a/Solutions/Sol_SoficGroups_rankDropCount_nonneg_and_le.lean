-- Prove2me | solution 1 for SoficGroups.rankDropCount_nonneg_and_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:52.29415+00:00
-- url     : https://prove2.me/submissions/45c54f23-35f4-4f4a-9713-b9938b7125c0

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
    (u v : ι → ℝ) (H r : ℝ) :
    0 ≤ rankDropCount u v H r ∧
      rankDropCount u v H r ≤ (Fintype.card ι : ℝ) := by
  classical
  constructor
  · unfold rankDropCount
    exact Finset.sum_nonneg (fun i hi => by split_ifs <;> norm_num)
  · unfold rankDropCount
    calc
      (∑ i : ι, if ⌊(v i + r) / H⌋ < ⌊(u i + r) / H⌋
        then (1 : ℝ) else 0) ≤ ∑ _i : ι, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro i hi
          split_ifs <;> norm_num
      _ = (Fintype.card ι : ℝ) := by simp
end SoficGroups
