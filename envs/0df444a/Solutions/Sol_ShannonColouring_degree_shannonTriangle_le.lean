-- Prove2me | solution 1 for ShannonColouring.degree_shannonTriangle_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:24:32.500644+00:00
-- url     : https://prove2.me/submissions/09a67560-b594-4af3-bfd3-9808f193b41f

module
public import Definitions.Def_ShannonColouring_Defs
public import Definitions.Def_ShannonColouring_Sharp

set_option autoImplicit true
@[expose] public section
public section
open ShannonColouring
namespace ShannonColouring
theorem _root_.solution (Δ : ℕ) (v : Fin 3) : degree (shannonTriangle Δ) v ≤ Δ := by
  rw [degree, Finset.card_filter, Fintype.sum_sum_type, Fintype.sum_sum_type]
  obtain ⟨t, rfl | rfl⟩ := Nat.even_or_odd' Δ <;>
  fin_cases v <;> simp [shannonTriangle] <;> omega
end ShannonColouring
