-- Prove2me | solution 1 for ThreeSum.Arithmetic.sum_fiberWeight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:17:05.965875+00:00
-- url     : https://prove2.me/submissions/ad54c4e6-be44-4a67-b8aa-4fe0e5f19191

import Mathlib.Data.Int.ModEq
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_Arithmetic
import Theorems.Thm_ThreeSum_Arithmetic_missWeight_zero
attribute [local simp] ThreeSum.Arithmetic.missWeight_zero

set_option autoImplicit false
open ThreeSum ThreeSum.Arithmetic
open Finset
open scoped BigOperators
namespace ThreeSum.Arithmetic
theorem _root_.solution {ι τ : Type*} [Fintype τ] [DecidableEq τ]
    (I : Finset ι) (owner : ι → τ) (weight : ι → ℕ) :
    (∑ t : τ, fiberWeight I owner weight t) = ∑ i ∈ I, weight i := by
  classical
  unfold fiberWeight
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  simp
end ThreeSum.Arithmetic
