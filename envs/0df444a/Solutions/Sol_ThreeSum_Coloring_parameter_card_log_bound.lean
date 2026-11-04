-- Prove2me | solution 1 for ThreeSum.Coloring.parameter_card_log_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:47:09.971696+00:00
-- url     : https://prove2.me/submissions/179c2806-dff0-4d33-a841-6ac92cee96ef

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
import Theorems.Thm_ThreeSum_Coloring_parameter_card
import Theorems.Thm_ThreeSum_Coloring_indexWidth_le_log2

set_option autoImplicit false
open ThreeSum ThreeSum.Coloring
variable {α : Type*}
namespace ThreeSum.Coloring
theorem _root_.solution (n : ℕ) :
    Fintype.card (Parameter (indexWidth n)) ≤ 81 * (n.log2 + 1) ^ 2 := by
  rw [parameter_card]
  exact Nat.mul_le_mul_left 81 (Nat.pow_le_pow_left (indexWidth_le_log2 n) 2)
end ThreeSum.Coloring
