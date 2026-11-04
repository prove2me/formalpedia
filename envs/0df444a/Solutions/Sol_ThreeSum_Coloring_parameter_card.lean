-- Prove2me | solution 1 for ThreeSum.Coloring.parameter_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:25:50.743193+00:00
-- url     : https://prove2.me/submissions/9b3ed135-ac38-41d3-afb5-283e587ac5d3

import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Size
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Image
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_Coloring

set_option autoImplicit false
open ThreeSum ThreeSum.Coloring
variable {α : Type*}
namespace ThreeSum.Coloring
theorem _root_.solution (d : ℕ) : Fintype.card (Parameter d) = 81 * d ^ 2 := by
  simp [Parameter, Fintype.card_fun, pow_two, Nat.mul_comm, Nat.mul_left_comm,
    Nat.mul_assoc]
end ThreeSum.Coloring
