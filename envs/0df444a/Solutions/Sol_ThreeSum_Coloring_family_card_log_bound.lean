-- Prove2me | solution 1 for ThreeSum.Coloring.family_card_log_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:47:11.195828+00:00
-- url     : https://prove2.me/submissions/5ae2267b-38c3-459c-90be-5dc58782f17f

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
import Theorems.Thm_ThreeSum_Coloring_indexWidth_le_log2
import Theorems.Thm_ThreeSum_Coloring_family_card_bound

set_option autoImplicit false
open ThreeSum ThreeSum.Coloring
variable {α : Type*}
namespace ThreeSum.Coloring
theorem _root_.solution (n : ℕ) :
    (family n).card ≤ 81 * (n.log2 + 1) ^ 2 := by
  exact (family_card_bound n).trans
    (Nat.mul_le_mul_left 81 (Nat.pow_le_pow_left (indexWidth_le_log2 n) 2))
end ThreeSum.Coloring
