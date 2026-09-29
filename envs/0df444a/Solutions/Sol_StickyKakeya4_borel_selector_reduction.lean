-- Prove2me | solution 1 for StickyKakeya4.borel_selector_reduction
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @sensei
-- created : 2026-09-27T12:48:47.901962+00:00
-- url     : https://prove2.me/submissions/3796ad27-392d-4e21-a134-c46581d10f2a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_StickyKakeya4_compact_full_direction_borel_selector
import Theorems.Thm_StickyKakeya4_direction_selector_packingDim_lower

open MeasureTheory Set
open StickyKakeya4

private theorem lineCarrier_mono_aux {s t : Set MarkedLine} (hst : s ⊆ t) :
    lineCarrier s ⊆ lineCarrier t := by
  exact Set.image_mono hst

private theorem packingDim_mono_aux {X : Type*} [PseudoMetricSpace X]
    {s t : Set X} (hst : s ⊆ t) : packingDim s ≤ packingDim t := by
  apply sInf_le_sInf
  intro d hd
  obtain ⟨pieces, ht, hpieces⟩ := hd
  exact ⟨pieces, hst.trans ht, hpieces⟩

theorem solution (lines : Set MarkedLine)
    (hsticky : IsStickyDatum lines) :
    ∃ selector : Set MarkedLine,
      MeasurableSet selector ∧
      selector ⊆ lines ∧
      IsDirectionSelector selector ∧
      packingDim (lineCarrier selector) = 3 ∧
      unitFront selector ⊆ unitFront lines := by
  obtain ⟨selector, hmeasurable, hsubset, hselector⟩ :=
    compact_full_direction_borel_selector lines hsticky.1 hsticky.2.2.1
  refine ⟨selector, hmeasurable, hsubset, hselector, ?_, ?_⟩
  · apply le_antisymm
    · calc
        packingDim (lineCarrier selector) ≤ packingDim (lineCarrier lines) :=
          packingDim_mono_aux (lineCarrier_mono_aux hsubset)
        _ = 3 := hsticky.2.2.2
    · exact direction_selector_packingDim_lower selector hselector
  · rintro x ⟨line, hline, t, ht, rfl⟩
    exact ⟨line, hsubset hline, t, ht, rfl⟩
