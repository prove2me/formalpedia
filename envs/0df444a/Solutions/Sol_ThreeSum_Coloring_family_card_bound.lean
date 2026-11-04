-- Prove2me | solution 1 for ThreeSum.Coloring.family_card_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:25:14.406208+00:00
-- url     : https://prove2.me/submissions/3bd978e4-24e0-4a47-9f5f-70832e1512eb

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

set_option autoImplicit false
open ThreeSum ThreeSum.Coloring
variable {α : Type*}
namespace ThreeSum.Coloring
theorem _root_.solution (n : ℕ) :
    (family n).card ≤ 81 * (indexWidth n) ^ 2 := by
  calc
    (family n).card ≤ Fintype.card (Parameter (indexWidth n)) :=
      Finset.card_image_le
    _ = _ := parameter_card _
end ThreeSum.Coloring
