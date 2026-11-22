-- Prove2me | solution 1 for SZ.natCast_mem_MahlerZ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:54:48.524189+00:00
-- url     : https://prove2.me/submissions/98c06dce-322e-46a0-80cf-6fb02adde127

import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Definitions.Def_SZ_Defs

set_option autoImplicit false
open SZ
open Int
namespace SZ
theorem _root_.solution {g : ℕ} (hg : 2 ≤ g) : (g : ℝ) ∈ MahlerZ := by
  refine ⟨by exact_mod_cast hg.trans_lt' one_lt_two, 2, two_ne_zero, fun n _ => ?_⟩
  have e : (2 : ℝ) * (g : ℝ) ^ n = ((2 * (g : ℤ) ^ n : ℤ) : ℝ) := by push_cast; ring
  rw [e, Int.floor_intCast]
  exact ⟨(g : ℤ) ^ n, by ring⟩
end SZ
