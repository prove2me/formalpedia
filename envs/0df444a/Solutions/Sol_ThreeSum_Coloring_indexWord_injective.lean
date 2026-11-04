-- Prove2me | solution 1 for ThreeSum.Coloring.indexWord_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:29:07.876334+00:00
-- url     : https://prove2.me/submissions/91ca8306-52c4-40ff-adc1-e0c4611afa57

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
import Theorems.Thm_ThreeSum_Coloring_index_lt_pow_width

set_option autoImplicit false
open ThreeSum ThreeSum.Coloring
variable {α : Type*}
namespace ThreeSum.Coloring
theorem _root_.solution (n : ℕ) : Function.Injective (@indexWord n) := by
  intro i j hij
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < indexWidth n
  · exact congrFun hij ⟨k, hk⟩
  · have hp : 2 ^ indexWidth n ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_eq_false_of_lt ((index_lt_pow_width i).trans_le hp),
      Nat.testBit_eq_false_of_lt ((index_lt_pow_width j).trans_le hp)]
end ThreeSum.Coloring
