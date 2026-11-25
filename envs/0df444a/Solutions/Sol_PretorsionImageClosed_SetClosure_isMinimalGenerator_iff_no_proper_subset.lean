-- Prove2me | solution 1 for PretorsionImageClosed.SetClosure.isMinimalGenerator_iff_no_proper_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:18:16.9455+00:00
-- url     : https://prove2.me/submissions/db047f77-c9dd-48c1-9790-7cc327a11113

module
public import Mathlib.Data.Set.Card
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_Basic
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_Finite

set_option autoImplicit true
@[expose] public section
public section
open Set
open PretorsionImageClosed PretorsionImageClosed.SetClosure
variable {E : Type*} {c : SetClosure E}
namespace PretorsionImageClosed.SetClosure
theorem _root_.solution
    {B C : Set E} :
    c.IsMinimalGenerator B C ↔
      c B = C ∧ ∀ ⦃D : Set E⦄, D ⊂ B → c D ≠ C := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    intro D hDB hDC
    obtain ⟨b, hbB, hbD⟩ := Set.exists_of_ssubset hDB
    apply h.2 hbB
    apply Set.Subset.antisymm
    · calc
        c (B \ {b}) ⊆ c B := c.monotone sdiff_subset
        _ = C := h.1
    · calc
        C = c D := hDC.symm
        _ ⊆ c (B \ {b}) := c.monotone fun x hxD ↦
          ⟨hDB.subset hxD, fun hxb ↦ hbD (hxb ▸ hxD)⟩
  · rintro ⟨hBC, hminimal⟩
    refine ⟨hBC, ?_⟩
    intro b hbB
    apply hminimal
    rw [Set.ssubset_iff_subset_ne]
    refine ⟨sdiff_subset, ?_⟩
    intro heq
    have : b ∈ B \ {b} := heq.symm ▸ hbB
    exact this.2 rfl
end PretorsionImageClosed.SetClosure
