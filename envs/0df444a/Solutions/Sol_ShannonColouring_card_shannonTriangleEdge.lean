-- Prove2me | solution 1 for ShannonColouring.card_shannonTriangleEdge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:25:13.399872+00:00
-- url     : https://prove2.me/submissions/67e792ea-dfce-4d73-9bce-da82940ded26

module
public import Definitions.Def_ShannonColouring_Defs
public import Definitions.Def_ShannonColouring_Sharp

set_option autoImplicit true
@[expose] public section
public section
open ShannonColouring
namespace ShannonColouring
theorem _root_.solution (Δ : ℕ) : Fintype.card (ShannonTriangleEdge Δ) = 3 * Δ / 2 := by
  simp only [Fintype.card_sum, Fintype.card_fin]
  obtain ⟨t, rfl | rfl⟩ := Nat.even_or_odd' Δ <;> omega
end ShannonColouring
