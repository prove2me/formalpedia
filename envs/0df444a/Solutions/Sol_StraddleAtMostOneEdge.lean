-- Prove2me | solution 1 for StraddleAtMostOneEdge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:09:42.14422+00:00
-- url     : https://prove2.me/submissions/8243d408-fed7-4f56-8ef9-a7b9e39b7a9b

import Definitions.Def_Tablet_Preamble
import Definitions.Def_Tablet_StraddleAtMostOneEdge

set_option autoImplicit false
open Set
theorem _root_.solution (k : ℕ) (s : ℕ → ℝ) (c : ℝ)
    (hmono : MonotoneOn s (Set.Icc 0 k)) :
    ((Finset.Icc 1 k).filter (fun j => s (j - 1) < c ∧ c < s j)).card ≤ 1 := by
-- BODY
  have hm : ∀ p q : ℕ, p ≤ q → q ≤ k → s p ≤ s q := by
    intro p q hpq hq
    exact hmono (Set.mem_Icc.mpr ⟨Nat.zero_le _, hpq.trans hq⟩)
      (Set.mem_Icc.mpr ⟨Nat.zero_le _, hq⟩) hpq
  rw [Finset.card_le_one]
  intro x hx y hy
  simp only [Finset.mem_filter, Finset.mem_Icc] at hx hy
  obtain ⟨⟨hx1, hxk⟩, hxl, hxr⟩ := hx
  obtain ⟨⟨hy1, hyk⟩, hyl, hyr⟩ := hy
  by_contra hne
  rcases Nat.lt_or_ge x y with h | h
  · have hle : s x ≤ s (y - 1) := hm x (y - 1) (by omega) (by omega)
    linarith
  · have hxy : y < x := by omega
    have hle : s y ≤ s (x - 1) := hm y (x - 1) (by omega) (by omega)
    linarith
