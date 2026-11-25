-- Prove2me | solution 1 for SZ.digitSum_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:52:30.478987+00:00
-- url     : https://prove2.me/submissions/2463848e-16c8-472a-8530-e894e1c13a00

import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_SZ_DigitParity
import Theorems.Thm_SZ_digitSum_monotone
import Theorems.Thm_SZ_bddAbove_digitSum

set_option autoImplicit false
open SZ
open Finset Filter Topology
variable {m : ℕ} {d : ℕ → ℤ}
namespace SZ
theorem _root_.solution (h : IsDigits m d) :
    Tendsto (digitSum m d) atTop (𝓝 (digitReal m d)) :=
  tendsto_atTop_ciSup (digitSum_monotone h) (bddAbove_digitSum h)
end SZ
