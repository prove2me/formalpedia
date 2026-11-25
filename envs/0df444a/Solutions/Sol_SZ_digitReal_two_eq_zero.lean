-- Prove2me | solution 1 for SZ.digitReal_two_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:03:09.397847+00:00
-- url     : https://prove2.me/submissions/3debfb4e-754b-4fdb-965d-8229a486cda2

import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_SZ_DigitParity
import Theorems.Thm_SZ_digitSum_le_digitReal

set_option autoImplicit false
open SZ
open Finset Filter Topology
variable {m : ℕ} {d : ℕ → ℤ}
namespace SZ
theorem _root_.solution {d : ℕ → ℤ} (h : IsDigits 2 d) (hev : ∀ i, Even (d i)) :
    digitReal 2 d = 0 := by
  have hz : ∀ i, d i = 0 := by
    intro i
    have h1 := h.nonneg i
    have h2 := h.le_sub_one i
    have h3 := hev i
    rw [Int.even_iff] at h3
    omega
  have : ∀ k, digitSum 2 d k = 0 := by
    intro k; simp [digitSum, hz]
  refine le_antisymm (ciSup_le fun k => by rw [this]) ?_
  simpa [this 0] using digitSum_le_digitReal h 0
end SZ
