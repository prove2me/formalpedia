-- Prove2me | solution 1 for SZ.even_floor_add_digitReal_mul_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:26:53.567928+00:00
-- url     : https://prove2.me/submissions/b2cb7132-5fca-46b0-9cd1-a605ebbd8370

import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_SZ_DigitParity
import Theorems.Thm_SZ_dvd_floor_add_digitReal_mul_pow

set_option autoImplicit false
open SZ
open Finset Filter Topology
variable {m : ℕ} {d : ℕ → ℤ}
namespace SZ
theorem _root_.solution (h : IsDigits m d) {N : ℤ} (hN : Even N)
    (hev : ∀ i, Even (d i)) (s : ℕ) {i₀ : ℕ} (hk : s ≤ i₀) (hsmall : d i₀ ≤ (m : ℤ) - 2) :
    Even ⌊((N : ℝ) + digitReal m d) * (m : ℝ) ^ s⌋ := by
  rw [even_iff_two_dvd]
  exact dvd_floor_add_digitReal_mul_pow h (even_iff_two_dvd.mp hN)
    (fun i => even_iff_two_dvd.mp (hev i)) s hk hsmall
end SZ
