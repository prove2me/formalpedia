-- Prove2me | solution 1 for SoficGroups.exists_common_rank_offset_one_sided_sharp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:52.29415+00:00
-- url     : https://prove2.me/submissions/a47ef383-ef0c-41c9-a9e4-aef6e133f1cf

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_rankDropCount_clamp_eq
import Theorems.Thm_SoficGroups_exists_common_rank_offset_bound_sharp

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution
    {ι : Type*} [Fintype ι]
    (u v delta : ι → ℝ) (H : ℝ) (hH : 0 < H)
    (hdelta : ∀ i : ι, 0 ≤ delta i)
    (hone : ∀ i : ι, u i - delta i ≤ v i) :
    ∃ r ∈ Set.Ico 0 H,
      rankDropCount u v H r ≤
        (1 / H) * ∑ i : ι, delta i := by
  classical
  obtain ⟨r, hr, hbound⟩ :=
    exists_common_rank_offset_bound_sharp
      u (fun i => min (v i) (u i))
      H hH (fun i => min_le_right (v i) (u i))
  refine ⟨r, hr, ?_⟩
  have hsum :
      (∑ i : ι, (u i - min (v i) (u i))) ≤
        ∑ i : ι, delta i := by
    apply Finset.sum_le_sum
    intro i hi
    by_cases hle : v i ≤ u i
    · rw [min_eq_left hle]
      linarith [hone i]
    · rw [min_eq_right (le_of_not_ge hle), sub_self]
      exact hdelta i
  calc
    rankDropCount u v H r =
      rankDropCount u (fun i => min (v i) (u i)) H r :=
        rankDropCount_clamp_eq u v H r hH
    _ ≤ (1 / H) * ∑ i : ι, (u i - min (v i) (u i)) := hbound
    _ ≤ (1 / H) * ∑ i : ι, delta i :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
end SoficGroups
