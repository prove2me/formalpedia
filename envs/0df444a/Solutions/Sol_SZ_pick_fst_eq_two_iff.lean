-- Prove2me | solution 1 for SZ.pick_fst_eq_two_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:05:12.472981+00:00
-- url     : https://prove2.me/submissions/a8ac65f6-8972-4d75-8f63-b3ca6e17cd20

import Definitions.Def_SZ_DigitParity
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_SZ_CoverGame
import Theorems.Thm_SZ_pick_cases
section
namespace SZ
open Filter Topology
private theorem s3_lb : (1.7 : ℝ) < Real.sqrt 3 :=
  (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
end SZ
end

set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution (w : ℝ) :
    (pick w).1 = 2 ↔ ((1 + Real.sqrt 3 < w ∧ w < 2 * Real.sqrt 3) ∨ 1 + 3 * Real.sqrt 3 < w) := by
  rcases pick_cases w with ⟨hw, hp⟩ | ⟨h1, h2, hp⟩ | ⟨h1, h2, hp⟩ | ⟨hw, hp⟩ <;> rw [hp]
  · constructor
    · intro h; exact absurd h (by norm_num)
    · rintro (⟨hx, _⟩ | hx) <;> linarith [s3_lb]
  · exact ⟨fun _ => Or.inl ⟨h1, h2⟩, fun _ => rfl⟩
  · constructor
    · intro h; exact absurd h (by norm_num)
    · rintro (⟨_, hx⟩ | hx) <;> linarith
  · exact ⟨fun _ => Or.inr hw, fun _ => rfl⟩
end SZ
