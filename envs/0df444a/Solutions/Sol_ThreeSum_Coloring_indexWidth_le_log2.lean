-- Prove2me | solution 1 for ThreeSum.Coloring.indexWidth_le_log2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:28:49.993224+00:00
-- url     : https://prove2.me/submissions/f4b57a28-3752-4469-b335-4adf74d762f7

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
import Theorems.Thm_ThreeSum_Coloring_indexWidth_le

set_option autoImplicit false
open ThreeSum ThreeSum.Coloring
variable {α : Type*}
namespace ThreeSum.Coloring
theorem _root_.solution (n : ℕ) : indexWidth n ≤ n.log2 + 1 :=
  indexWidth_le Nat.lt_log2_self.le
end ThreeSum.Coloring
