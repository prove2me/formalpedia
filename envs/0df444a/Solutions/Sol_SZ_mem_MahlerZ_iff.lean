-- Prove2me | solution 1 for SZ.mem_MahlerZ_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:54:34.146587+00:00
-- url     : https://prove2.me/submissions/3153f7e6-86cb-406f-beb9-bcef3c58714c

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
theorem _root_.solution {α : ℝ} :
    α ∈ MahlerZ ↔ 1 < α ∧ ∃ ξ : ℝ, ξ ≠ 0 ∧ ∀ n : ℕ, 1 ≤ n → Even ⌊ξ * α ^ n⌋ := Iff.rfl
end SZ
