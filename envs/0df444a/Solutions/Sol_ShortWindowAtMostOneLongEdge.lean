-- Prove2me | solution 1 for ShortWindowAtMostOneLongEdge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:06:04.144266+00:00
-- url     : https://prove2.me/submissions/e57a4934-616f-4433-93be-8a7d55e400ad

import Definitions.Def_Tablet_Preamble
import Definitions.Def_Tablet_ShortWindowAtMostOneLongEdge

set_option autoImplicit false
open Set
theorem _root_.solution (K : ℕ) (sA : ℕ → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hmono : MonotoneOn sA (Set.Icc 0 K))
    (hshort : sA (K - 1) - sA 1 ≤ δ) :
    ((Finset.Icc 2 (K - 1)).filter (fun i => δ ≤ sA i - sA (i - 1))).card ≤ 1 := by
-- BODY
  have m : ∀ a b : ℕ, a ≤ b → b ≤ K → sA a ≤ sA b := by
    intro a b hab hb
    exact hmono (Set.mem_Icc.mpr ⟨Nat.zero_le _, le_trans hab hb⟩)
      (Set.mem_Icc.mpr ⟨Nat.zero_le _, hb⟩) hab
  have key : ∀ x y : ℕ, 2 ≤ x → x ≤ K - 1 → 2 ≤ y → y ≤ K - 1 →
      δ ≤ sA x - sA (x - 1) → δ ≤ sA y - sA (y - 1) → x < y → False := by
    intro x y hx2 hxK hy2 hyK hxl hyl hxy
    have h1 : sA x ≤ sA (y - 1) := m x (y - 1) (by omega) (by omega)
    have h2 : sA 1 ≤ sA (x - 1) := m 1 (x - 1) (by omega) (by omega)
    have h3 : sA y ≤ sA (K - 1) := m y (K - 1) (by omega) (by omega)
    linarith
  rw [Finset.card_le_one]
  intro x hx y hy
  simp only [Finset.mem_filter, Finset.mem_Icc] at hx hy
  obtain ⟨⟨hx2, hxK⟩, hxl⟩ := hx
  obtain ⟨⟨hy2, hyK⟩, hyl⟩ := hy
  rcases lt_trichotomy x y with h | h | h
  · exact absurd (key x y hx2 hxK hy2 hyK hxl hyl h) not_false
  · exact h
  · exact absurd (key y x hy2 hyK hx2 hxK hyl hxl h) not_false
