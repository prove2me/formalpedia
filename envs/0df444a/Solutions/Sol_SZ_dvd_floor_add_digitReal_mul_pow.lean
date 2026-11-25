-- Prove2me | solution 1 for SZ.dvd_floor_add_digitReal_mul_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:25:56.868938+00:00
-- url     : https://prove2.me/submissions/c597c142-5455-4847-b5af-6cb9b9075ce9

import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_SZ_DigitParity
import Theorems.Thm_SZ_floor_add_digitReal_mul_pow

set_option autoImplicit false
open SZ
open Finset Filter Topology
variable {m : ℕ} {d : ℕ → ℤ}
namespace SZ
theorem _root_.solution (h : IsDigits m d) {p N : ℤ} (hN : p ∣ N)
    (hdvd : ∀ i, p ∣ d i) (s : ℕ) {i₀ : ℕ} (hk : s ≤ i₀) (hsmall : d i₀ ≤ (m : ℤ) - 2) :
    p ∣ ⌊((N : ℝ) + digitReal m d) * (m : ℝ) ^ s⌋ := by
  rw [floor_add_digitReal_mul_pow h N s hk hsmall]
  exact dvd_add (hN.mul_right _) (Finset.dvd_sum fun i _ => (hdvd i).mul_right _)
end SZ
