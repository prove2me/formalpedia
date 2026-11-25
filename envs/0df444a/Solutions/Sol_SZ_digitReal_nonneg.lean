-- Prove2me | solution 1 for SZ.digitReal_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:24:38.844639+00:00
-- url     : https://prove2.me/submissions/7dc0a8ea-262e-4aad-bc09-644a4a6745a3

import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_SZ_DigitParity
import Theorems.Thm_SZ_digitSum_nonneg
import Theorems.Thm_SZ_digitSum_le_digitReal

set_option autoImplicit false
open SZ
open Finset Filter Topology
variable {m : ℕ} {d : ℕ → ℤ}
namespace SZ
theorem _root_.solution (h : IsDigits m d) : 0 ≤ digitReal m d :=
  le_trans (digitSum_nonneg h 0) (digitSum_le_digitReal h 0)
end SZ
