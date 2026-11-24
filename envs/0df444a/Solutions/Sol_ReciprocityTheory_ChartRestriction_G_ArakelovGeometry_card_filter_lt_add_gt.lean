-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.card_filter_lt_add_gt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:15:28.919254+00:00
-- url     : https://prove2.me/submissions/0f0c5890-7570-43a6-b4dc-f5db8d74bb49

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_SupportSubsetMonoBox
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AbsProdSubProdSubLinLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {α : Type*} [LinearOrder α] (s : Finset α) {i : α} (hi : i ∈ s) :
    (s.filter (· < i)).card + (s.filter (i < ·)).card ≤ s.card - 1 := by
  rw [← Finset.card_erase_of_mem hi, ← Finset.card_union_of_disjoint
    (Finset.disjoint_filter.mpr fun j _ h1 h2 => lt_asymm h1 h2)]
  refine Finset.card_le_card fun j hj => ?_
  simp only [Finset.mem_union, Finset.mem_filter] at hj
  rw [Finset.mem_erase]
  rcases hj with ⟨hj, h⟩ | ⟨hj, h⟩
  · exact ⟨ne_of_lt h, hj⟩
  · exact ⟨ne_of_gt h, hj⟩
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
