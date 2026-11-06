-- Prove2me | solution 1 for WhittFLT.TimeReversal.negRev_timeChange
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T04:48:22.730197+00:00
-- url     : https://prove2.me/submissions/49abcd71-ec06-4bc4-9526-c6c90e9323a9

import Mathlib
import Definitions.Def_WhittFLT_TimeReversal_Reversal

open Set

open WhittFLT.TimeReversal in
theorem solution (l : ℝ → ℝ) (hl : WhittFLT.Composition.IsTimeChange 0 1 l) :
    WhittFLT.Composition.IsTimeChange 0 1 (negRev l) ∧ EqOn (negRev id) id (Set.Icc 0 1) := by
  obtain ⟨hmono, hcont, himg⟩ := hl
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro t ht s hs hts
    unfold negRev
    have h1 : 1 - s ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have h2 : 1 - t ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have := hmono h1 h2 (by linarith)
    linarith
  · unfold negRev
    apply ContinuousOn.sub continuousOn_const
    apply hcont.comp (continuousOn_const.sub continuousOn_id)
    intro t ht
    simp only [Pi.sub_apply, id]
    exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
  · ext u
    constructor
    · rintro ⟨t, ht, rfl⟩
      have h2 : 1 - t ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
      have hm : l (1 - t) ∈ Icc (0 : ℝ) 1 := himg ▸ mem_image_of_mem l h2
      unfold negRev
      exact ⟨by linarith [hm.2], by linarith [hm.1]⟩
    · intro hu
      have h1 : 1 - u ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hu.2], by linarith [hu.1]⟩
      rw [← himg] at h1
      obtain ⟨s, hs, hsu⟩ := h1
      refine ⟨1 - s, ⟨by linarith [hs.2], by linarith [hs.1]⟩, ?_⟩
      unfold negRev
      rw [sub_sub_cancel, hsu]
      ring
  · intro t _
    simp [negRev]
