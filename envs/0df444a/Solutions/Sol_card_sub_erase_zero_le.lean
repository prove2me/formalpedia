-- Prove2me | solution 1 for card_sub_erase_zero_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:37:48.86871+00:00
-- url     : https://prove2.me/submissions/06f67889-12bd-4eb2-b6de-024c9b071795

import Mathlib.Order.Partition.Equipartition
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.UniformOn
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Definitions.Def_Polychromatic_ForMathlib_Misc

set_option autoImplicit true
open Finset
open Pointwise
theorem _root_.solution {G : Type*} [DecidableEq G] [AddGroup G] {S : Finset G} :
    #((S - S).erase 0) ≤ #S * (#S - 1) := by
  calc
    #((S - S).erase 0) = #((Finset.image₂ (· - ·) S S).erase 0) := rfl
    _ = #((S.biUnion fun x ↦ S.image (x - ·)).erase 0) := by rw [← biUnion_image_left]
    _ ≤ #(S.biUnion fun x ↦ (S.erase x).image (x - ·)) := by
      apply card_le_card
      simp only [subset_iff, mem_erase, ne_eq, mem_biUnion, mem_image, and_imp, forall_exists_index]
      intro _ ne x hx y hy rfl
      exact ⟨x, hx, y, ⟨by rintro rfl; simp at ne, hy⟩, rfl⟩
    _ ≤ ∑ x ∈ S, #((S.erase x).image (x - ·)) := card_biUnion_le
    _ ≤ ∑ x ∈ S, #(S.erase x) := sum_le_sum fun i hi ↦ card_image_le
    _ = _ := by simp +contextual [card_erase_of_mem]
