-- Prove2me | solution 1 for SZ.pick_snd_eq_two_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:04:14.448065+00:00
-- url     : https://prove2.me/submissions/d8349751-834d-4052-bec1-0f1445b57e98

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
theorem _root_.solution (w : ℝ) : (pick w).2 = 2 ↔ 2 * Real.sqrt 3 ≤ w := by
  rcases pick_cases w with ⟨hw, hp⟩ | ⟨h1, h2, hp⟩ | ⟨h1, h2, hp⟩ | ⟨hw, hp⟩ <;> rw [hp]
  · constructor
    · intro h; exact absurd h (by norm_num)
    · intro h; linarith [s3_lb]
  · constructor
    · intro h; exact absurd h (by norm_num)
    · intro h; linarith
  · exact ⟨fun _ => h1, fun _ => rfl⟩
  · exact ⟨fun _ => by linarith [s3_lb], fun _ => rfl⟩
end SZ
