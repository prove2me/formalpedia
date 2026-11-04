-- Prove2me | solution 1 for ThreeSum.Coloring.index_lt_pow_width
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:25:12.071873+00:00
-- url     : https://prove2.me/submissions/4f2ccf1a-5f97-49fe-98cf-be577e0ed14b

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
theorem _root_.solution {n : ℕ} (i : Fin n) : i.val < 2 ^ indexWidth n := by
  exact (show i.val ≤ n - 1 by omega).trans_lt (Nat.lt_size_self (n - 1))
end ThreeSum.Coloring
