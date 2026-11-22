-- Prove2me | solution 1 for SZ.mem_MahlerZ_of_floor_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:52:53.897547+00:00
-- url     : https://prove2.me/submissions/0a67edc8-e5b7-4049-9362-f4eb4d6348b7

import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Definitions.Def_SZ_Defs
import Theorems.Thm_SZ_mem_MahlerZ_of_eventually

set_option autoImplicit false
open SZ
open Int
namespace SZ
theorem _root_.solution {α ξ : ℝ} (hα : 1 < α) (hξ : ξ ≠ 0) (N : ℕ) (x : ℕ → ℤ)
    (hx : ∀ n : ℕ, N ≤ n → Even (x n)) (hfl : ∀ n : ℕ, N ≤ n → ⌊ξ * α ^ n⌋ = x n) :
    α ∈ MahlerZ :=
  mem_MahlerZ_of_eventually hα hξ N fun n hn => (hfl n hn) ▸ hx n hn
end SZ
