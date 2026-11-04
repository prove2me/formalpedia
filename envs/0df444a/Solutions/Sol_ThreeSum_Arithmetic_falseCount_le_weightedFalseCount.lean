-- Prove2me | solution 1 for ThreeSum.Arithmetic.falseCount_le_weightedFalseCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:17:04.922921+00:00
-- url     : https://prove2.me/submissions/a3729242-860d-4eca-a03b-c818341f167f

import Mathlib.Data.Int.ModEq
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_Arithmetic
import Theorems.Thm_ThreeSum_Arithmetic_missWeight_pos_of_witness
import Theorems.Thm_ThreeSum_Arithmetic_missWeight_zero
attribute [local simp] ThreeSum.Arithmetic.missWeight_zero

set_option autoImplicit false
open ThreeSum ThreeSum.Arithmetic
open Finset
open scoped BigOperators
namespace ThreeSum.Arithmetic
theorem _root_.solution {ι : Type*} (T : Finset ι)
    (difference : ι → ℤ) (L : Finset ℤ) (m : ℤ)
    (hsep : ∀ i ∈ T, difference i ≠ 0 → ∃ l ∈ L, ¬ l ∣ difference i) :
    (∑ i ∈ T, if m ∣ difference i ∧ difference i ≠ 0 then (1 : ℕ) else 0) ≤
      weightedFalseCount T difference L m := by
  unfold weightedFalseCount
  apply Finset.sum_le_sum
  intro i hi
  by_cases h : m ∣ difference i ∧ difference i ≠ 0
  · obtain ⟨l, hl, hnot⟩ := hsep i hi h.2
    simpa [h, h.1] using missWeight_pos_of_witness hl hnot
  · simp only [if_neg h]
    exact Nat.zero_le _
end ThreeSum.Arithmetic
