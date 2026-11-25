-- Prove2me | solution 1 for SZ.zones_of_not_InO
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:40:50.386397+00:00
-- url     : https://prove2.me/submissions/3c6e57c4-3bb1-4a25-8930-3fc487a94d38

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree

set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution {w : ℝ} (hO : ¬ InO w) :
    w < 2 ∨ (1 + Real.sqrt 3 < w ∧ w < 2 * Real.sqrt 3) ∨
      (3 + Real.sqrt 3 < w ∧ w < 2 + 2 * Real.sqrt 3) ∨ 1 + 3 * Real.sqrt 3 < w := by
  rw [InO] at hO
  push Not at hO
  obtain ⟨hA, hB, hC⟩ := hO
  rcases lt_or_ge w 2 with hx | hx
  · exact Or.inl hx
  · have h2 : 1 + Real.sqrt 3 < w := hA hx
    rcases lt_or_ge w (2 * Real.sqrt 3) with hy | hy
    · exact Or.inr (Or.inl ⟨h2, hy⟩)
    · have h4 : 3 + Real.sqrt 3 < w := hB hy
      rcases lt_or_ge w (2 + 2 * Real.sqrt 3) with hz | hz
      · exact Or.inr (Or.inr (Or.inl ⟨h4, hz⟩))
      · exact Or.inr (Or.inr (Or.inr (hC hz)))
end SZ
