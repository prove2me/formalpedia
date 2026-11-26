-- Prove2me | solution 1 for add_succ_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:46:56.243668+00:00
-- url     : https://prove2.me/submissions/2d50b6a7-1e84-453a-9cb9-d072c84bc42f

import Definitions.Def_CARDB
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_CARDB_Asymptotics

set_option autoImplicit true
open Set TopologicalSpace
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {x y : α}
theorem _root_.solution (k : ℕ) : (k + 1) ^ 2 + (k + 1) = k ^ 2 + k + 2 * k + 2 := by
  ring
