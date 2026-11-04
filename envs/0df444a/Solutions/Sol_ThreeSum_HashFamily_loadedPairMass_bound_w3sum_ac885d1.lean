-- Prove2me | solution 1 for ThreeSum.HashFamily.loadedPairMass_bound_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:15:14.333198+00:00
-- url     : https://prove2.me/submissions/6974fc9a-9b24-403b-9abe-e12a9864f667

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
import Theorems.Thm_ThreeSum_HashFamily_pairEvent_card
import Theorems.Thm_ThreeSum_HashFamily_tripleEvent_card
import Theorems.Thm_ThreeSum_HashFamily_sum_filtered_cards
attribute [local simp] ThreeSum.HashFamily.hashMap_apply

set_option autoImplicit false
open ThreeSum ThreeSum.HashFamily
open scoped BigOperators
variable {α K : Type*}
variable [Fintype α] [DecidableEq α] [Field K] [Fintype K] [DecidableEq K]
namespace ThreeSum.HashFamily
theorem _root_.solution {s t : α → Bool} (hst : s ≠ t) (a b : K)
    (vertices : Finset (α → Bool)) (hcross : ∀ u ∈ vertices, u ≠ t) :
    Fintype.card K ^ 3 * loadedPairMass s t a b vertices ≤
      (Fintype.card K + vertices.card) * Fintype.card (α × Bool → K) := by
  unfold loadedPairMass bucketSize
  rw [sum_filtered_cards, Finset.mul_sum]
  have hterm : ∀ u ∈ vertices, Fintype.card K ^ 3 *
      ((pairEvent s t a b).filter (fun w => hashValue w u = a)).card ≤
        Fintype.card (α × Bool → K) * (1 + if u = s then Fintype.card K else 0) := by
    intro u hu
    by_cases he : u = s
    · subst u
      have hfilter : (pairEvent s t a b).filter (fun w => hashValue w s = a) =
          pairEvent s t a b := by
        ext w
        constructor
        · intro hw
          exact (Finset.mem_filter.mp hw).1
        · intro hw
          exact Finset.mem_filter.mpr ⟨hw, (Finset.mem_filter.mp hw).2.1⟩
      rw [hfilter]
      have hc := pairEvent_card hst a b
      calc
        _ = Fintype.card K * (Fintype.card K ^ 2 * (pairEvent s t a b).card) := by ring
        _ = Fintype.card K * Fintype.card (α × Bool → K) := by rw [hc]
        _ ≤ _ := by
          simp only [ite_true]
          rw [Nat.mul_comm (Fintype.card K)]
          exact Nat.mul_le_mul_left _ (by omega)
    · have hfilter : (pairEvent s t a b).filter (fun w => hashValue w u = a) =
          wordEvent ![s, t, u] ![a, b, a] := by
        ext w
        simp [pairEvent, wordEvent, Fin.forall_fin_succ, and_assoc]
      rw [hfilter, tripleEvent_card hst (Ne.symm he) (Ne.symm (hcross u hu)) a b a]
      simp [he]
  calc
    _ ≤ ∑ u ∈ vertices, Fintype.card (α × Bool → K) *
        (1 + if u = s then Fintype.card K else 0) := Finset.sum_le_sum hterm
    _ ≤ _ := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib]
      by_cases hs : s ∈ vertices
      · simp [hs, Nat.mul_comm, Nat.add_comm]
      · simp only [Finset.sum_const, smul_eq_mul, mul_one,
          Finset.sum_ite_eq', if_neg hs, add_zero]
        rw [Nat.mul_comm (Fintype.card (α × Bool → K))]
        exact Nat.mul_le_mul_right _ (by omega)
end ThreeSum.HashFamily
