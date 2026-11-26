-- Prove2me | solution 1 for SubResolutionShortEdgeCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:13:00.905353+00:00
-- url     : https://prove2.me/submissions/9241416c-4894-4805-9abd-44ddd5bb2b90

import Definitions.Def_Tablet_Preamble
import Definitions.Def_Tablet_SubResolutionShortEdgeCount

set_option autoImplicit false
open Set
theorem _root_.solution (c d : ℕ) (s : ℕ → ℝ) (δ : ℝ) :
    ((Finset.Icc 1 (d - c)).filter
        (fun j => (s (c + j) - s c) - (s (c + (j - 1)) - s c) < δ)).card
      = ((Finset.Ioc c d).filter (fun i => s i - s (i - 1) < δ)).card := by
-- BODY
  classical
  have himg : (Finset.Ioc c d).filter (fun i => s i - s (i - 1) < δ)
      = ((Finset.Icc 1 (d - c)).filter
          (fun j => (s (c + j) - s c) - (s (c + (j - 1)) - s c) < δ)).image (fun j => c + j) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_image, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨i - c, ⟨⟨by omega, by omega⟩, ?_⟩, by omega⟩
      have e1 : c + (i - c) = i := by omega
      have e2 : c + (i - c - 1) = i - 1 := by omega
      rw [e1, e2]
      linarith
    · rintro ⟨j, ⟨⟨hj1, hj2⟩, hj3⟩, rfl⟩
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      have e2 : c + j - 1 = c + (j - 1) := by omega
      rw [e2]
      linarith
  have hinj : Function.Injective (fun j : ℕ => c + j) := fun a b h => Nat.add_left_cancel h
  rw [himg, Finset.card_image_of_injective _ hinj]
