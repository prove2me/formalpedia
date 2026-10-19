-- Prove2me | solution 1 for SoficGroups.exists_common_rank_offset_bound_sharp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:52.29415+00:00
-- url     : https://prove2.me/submissions/ed3c7c2b-7b4f-4773-a48c-3970dd1f4dfc

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_exists_common_rank_offset
import Theorems.Thm_SoficGroups_rankDropCount_average_eq
import Theorems.Thm_SoficGroups_rankDrop_measureReal_bound_sharp

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution {ι : Type*} [Fintype ι]
    (u v : ι → ℝ) (H : ℝ) (hH : 0 < H)
    (hvu : ∀ i : ι, v i ≤ u i) :
    ∃ r ∈ Set.Ico 0 H,
      rankDropCount u v H r ≤
        (1 / H) * ∑ i : ι, (u i - v i) := by
  classical
  obtain ⟨r, hr, hmean⟩ := exists_common_rank_offset u v H hH
  refine ⟨r, hr, hmean.trans ?_⟩
  rw [rankDropCount_average_eq u v H hH]
  have hsum :
      (∑ i : ι, (MeasureTheory.volume.restrict (Set.Ico 0 H)).real
          {r : ℝ | ⌊(v i + r) / H⌋ < ⌊(u i + r) / H⌋}) ≤
        ∑ i : ι, (u i - v i) := by
    exact Finset.sum_le_sum (fun i hi =>
      rankDrop_measureReal_bound_sharp (u i) (v i) H hH (hvu i))
  calc
    H⁻¹ *
        (∑ i : ι, (MeasureTheory.volume.restrict (Set.Ico 0 H)).real
          {r : ℝ | ⌊(v i + r) / H⌋ < ⌊(u i + r) / H⌋}) ≤
      H⁻¹ * ∑ i : ι, (u i - v i) :=
        mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hH.le)
    _ = (1 / H) * ∑ i : ι, (u i - v i) := by
      rw [one_div]
end SoficGroups
