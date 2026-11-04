-- Prove2me | solution 1 for ThreeSum.Coloring.mem_negValues
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:08:12.883418+00:00
-- url     : https://prove2.me/submissions/563c9634-c775-494e-8f76-843b52c71b3a

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
import Theorems.Thm_ThreeSum_Coloring_mem_values

set_option autoImplicit false
open ThreeSum ThreeSum.Coloring
variable {α : Type*}
namespace ThreeSum.Coloring
theorem _root_.solution {n : ℕ} (x : Fin n → ℤ) (c : Fin n → Fin 3) (v : ℤ) :
    v ∈ negValues x c ↔ ∃ i, c i = 2 ∧ -x i = v := by
  simp [negValues, mem_values]
end ThreeSum.Coloring
