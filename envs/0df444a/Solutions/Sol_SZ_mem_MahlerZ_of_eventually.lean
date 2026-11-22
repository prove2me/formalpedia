-- Prove2me | solution 1 for SZ.mem_MahlerZ_of_eventually
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:52:15.203988+00:00
-- url     : https://prove2.me/submissions/50d2a666-52bc-46cd-bea8-6911e511b07c

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
theorem _root_.solution {α ξ : ℝ} (hα : 1 < α) (hξ : ξ ≠ 0) (N : ℕ)
    (h : ∀ n : ℕ, N ≤ n → Even ⌊ξ * α ^ n⌋) : α ∈ MahlerZ := by
  have hα0 : α ≠ 0 := ne_of_gt (lt_trans zero_lt_one hα)
  refine ⟨hα, ξ * α ^ N, mul_ne_zero hξ (pow_ne_zero N hα0), fun n hn => ?_⟩
  have e : ξ * α ^ N * α ^ n = ξ * α ^ (N + n) := by rw [pow_add]; ring
  rw [e]
  exact h _ (by omega)
end SZ
