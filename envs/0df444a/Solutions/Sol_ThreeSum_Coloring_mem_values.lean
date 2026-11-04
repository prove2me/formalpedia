-- Prove2me | solution 1 for ThreeSum.Coloring.mem_values
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:04:38.106701+00:00
-- url     : https://prove2.me/submissions/4a6cca59-d634-4cc4-8c9e-d46ddcc8bb23

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
theorem _root_.solution {n : ℕ} (x : Fin n → ℤ) (c : Fin n → Fin 3)
    (color : Fin 3) (v : ℤ) :
    v ∈ values x c color ↔ ∃ i, c i = color ∧ x i = v := by
  simp [values]
end ThreeSum.Coloring
