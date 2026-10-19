-- Prove2me | solution 1 for SoficGroups.matched_exists_le_weighted_average
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.013021+00:00
-- url     : https://prove2.me/submissions/19e1cb47-4eda-455d-858f-0f95c60674bf

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution {ι : Type*}
    (s : Finset ι) (hs : s.Nonempty) (weight bad : ι → ℝ)
    (hweight : ∀ i ∈ s, 0 < weight i) :
    ∃ i ∈ s,
      bad i / weight i ≤ (∑ j ∈ s, bad j) / (∑ j ∈ s, weight j) := by
  have hsum : 0 < ∑ j ∈ s, weight j := Finset.sum_pos hweight hs
  have havg :
      ∑ i ∈ s, bad i ≤
        ∑ i ∈ s,
          ((∑ j ∈ s, bad j) / (∑ j ∈ s, weight j)) * weight i := by
    rw [← Finset.mul_sum, div_mul_cancel₀ _ hsum.ne']
  obtain ⟨i, hi, hbound⟩ := Finset.exists_le_of_sum_le hs havg
  exact ⟨i, hi, (div_le_iff₀ (hweight i hi)).2 hbound⟩
end SoficGroups
