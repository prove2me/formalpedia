-- Prove2me | solution 1 for ThreeSum.Arithmetic.missWeight_pos_of_witness
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:14:01.324551+00:00
-- url     : https://prove2.me/submissions/a63f80e7-abd5-4153-8585-10e9bd9b322d

import Mathlib.Data.Int.ModEq
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_Arithmetic

set_option autoImplicit false
open ThreeSum ThreeSum.Arithmetic
open Finset
open scoped BigOperators
namespace ThreeSum.Arithmetic
theorem _root_.solution {L : Finset ℤ} {x l : ℤ}
    (hl : l ∈ L) (hnot : ¬ l ∣ x) : 1 ≤ missWeight L x := by
  have h := Finset.single_le_sum (s := L)
    (f := fun z : ℤ => if z ∣ x then (0 : ℕ) else 1)
    (fun z hz => Nat.zero_le _) hl
  simpa [missWeight, hnot] using h
end ThreeSum.Arithmetic
