-- Prove2me | solution 1 for StickyKakeya4.sticky_kakeya_four_dimensional
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @sensei
-- created : 2026-09-27T12:43:08.653663+00:00
-- url     : https://prove2.me/submissions/773a5492-6c3d-42e5-a784-b60a9ea11639
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_StickyKakeya4_borel_selector_reduction
import Theorems.Thm_StickyKakeya4_selector_closure

open MeasureTheory Set
open StickyKakeya4

theorem solution (lines : Set MarkedLine)
    (hsticky : IsStickyDatum lines) :
    dimH (unitFront lines) = 4 := by
  obtain ⟨selector, hmeasurable, hsubset, hselector, hpacking, hfront⟩ :=
    borel_selector_reduction lines hsticky
  have hvalid : ∀ line ∈ selector, IsValidLine line := by
    intro line hline
    exact hsticky.2.1 line (hsubset hline)
  have hselectorDim : dimH (unitFront selector) = 4 :=
    selector_closure selector hmeasurable hvalid hselector hpacking
  apply le_antisymm
  · calc
      dimH (unitFront lines) ≤ dimH (Set.univ : Set E4) :=
        dimH_mono (Set.subset_univ _)
      _ = 4 := by simp [E4, Real.dimH_univ_eq_finrank]
  · calc
      (4 : ENNReal) = dimH (unitFront selector) := hselectorDim.symm
      _ ≤ dimH (unitFront lines) := dimH_mono hfront
