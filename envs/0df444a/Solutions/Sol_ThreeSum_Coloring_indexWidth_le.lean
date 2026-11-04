-- Prove2me | solution 1 for ThreeSum.Coloring.indexWidth_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:25:13.218474+00:00
-- url     : https://prove2.me/submissions/793bebf0-4542-4cec-990d-4d97c742446b

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
theorem _root_.solution {n d : ℕ} (hn : n ≤ 2 ^ d) : indexWidth n ≤ d := by
  by_cases hzero : n = 0
  · simp [indexWidth, hzero]
  · exact Nat.size_le.mpr (by omega)
end ThreeSum.Coloring
