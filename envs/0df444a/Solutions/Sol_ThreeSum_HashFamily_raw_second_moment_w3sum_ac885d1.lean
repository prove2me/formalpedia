-- Prove2me | solution 1 for ThreeSum.HashFamily.raw_second_moment_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:25:08.985844+00:00
-- url     : https://prove2.me/submissions/49b6773b-7ec6-45c8-a445-d5061996f673

import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.Data.Fin.VecNotation
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_Submission_ThreeSum_HashFamily
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Definitions.Def_WeightedCache3SUM_Alias_e7677a02001e995b
import Theorems.Thm_ThreeSum_HashFamily_joint_pair_charge
attribute [local simp] ThreeSum.HashFamily.hashMap_apply

set_option autoImplicit false
open ThreeSum ThreeSum.HashFamily
open scoped BigOperators
variable {α K : Type*}
variable {E : Type*} [Fintype E] [DecidableEq E]
variable [Fintype α] [DecidableEq α] [Field K] [Fintype K] [DecidableEq K]
namespace ThreeSum.HashFamily
theorem _root_.solution (left right : E → α → Bool)
    (hinj : Function.Injective (fun e => (left e, right e)))
    (hcross : ∀ e f, left e ≠ right f)
    (B : ℕ) (hB : ∀ e, (badPartners left right e).card ≤ B) (a b : K) :
    Fintype.card K ^ 4 *
        (∑ w, incidenceCount (fun e => pairEvent (left e) (right e) a b) w ^ 2) ≤
      Fintype.card (α × Bool → K) *
        (Fintype.card E * Fintype.card K ^ 2 + Fintype.card E ^ 2 +
          Fintype.card E * B * Fintype.card K) := by
  have hrow : ∀ e : E, (∑ f : E, Fintype.card K ^ 4 *
      (pairEvent (left e) (right e) a b ∩ pairEvent (left f) (right f) a b).card) ≤
      Fintype.card (α × Bool → K) * (Fintype.card E + Fintype.card K ^ 2 + B * Fintype.card K) := by
    intro e
    calc
      _ ≤ ∑ f : E, Fintype.card (α × Bool → K) *
          (1 + (if e = f then Fintype.card K ^ 2 else 0) +
            (if f ∈ badPartners left right e then Fintype.card K else 0)) :=
        Finset.sum_le_sum (fun f hf => joint_pair_charge left right hinj hcross a b e f)
      _ = Fintype.card (α × Bool → K) *
          (Fintype.card E + Fintype.card K ^ 2 + (badPartners left right e).card * Fintype.card K) := by
        rw [← Finset.mul_sum]
        congr 1
        simp [Finset.sum_add_distrib]
      _ ≤ _ := by
        apply Nat.mul_le_mul_left
        exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (hB e)) _
  calc
    _ = ∑ e : E, ∑ f : E, Fintype.card K ^ 4 *
        (pairEvent (left e) (right e) a b ∩ pairEvent (left f) (right f) a b).card := by
      rw [sum_incidenceCount_sq, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e he
      exact Finset.mul_sum ..
    _ ≤ ∑ _e : E, Fintype.card (α × Bool → K) *
        (Fintype.card E + Fintype.card K ^ 2 + B * Fintype.card K) :=
      Finset.sum_le_sum (fun e he => hrow e)
    _ = _ := by simp; ring
end ThreeSum.HashFamily
