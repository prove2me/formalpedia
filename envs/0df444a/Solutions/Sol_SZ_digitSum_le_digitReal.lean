-- Prove2me | solution 1 for SZ.digitSum_le_digitReal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:45:43.923309+00:00
-- url     : https://prove2.me/submissions/017089a3-10dc-48f6-8505-58bfa3187fe3

import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_SZ_DigitParity
import Theorems.Thm_SZ_bddAbove_digitSum

set_option autoImplicit false
open SZ
open Finset Filter Topology
variable {m : ℕ} {d : ℕ → ℤ}
namespace SZ
theorem _root_.solution (h : IsDigits m d) (k : ℕ) :
    digitSum m d k ≤ digitReal m d :=
  le_ciSup (bddAbove_digitSum h) k
end SZ
