-- Prove2me | solution 1 for SoficGroups.ComponentMidrankVariance.sum_weighted_ordered_midpoints_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.013021+00:00
-- url     : https://prove2.me/submissions/0f6f3947-ac8f-414d-96b9-a9323c3df1b9

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
open SoficGroups.ComponentMidrankVariance
open scoped BigOperators
namespace SoficGroups.ComponentMidrankVariance
theorem _root_.solution (s : Finset ℤ) (w : ℤ → ℝ) :
    (∑ j ∈ s, w j * (lowerRankWeight s w j + w j / 2) ^ 2) =
      (∑ j ∈ s, w j) ^ 3 / 3 -
        (∑ j ∈ s, w j ^ 3) / 12 := by
  classical
  induction s using Finset.induction_on_max with
  | empty => simp [lowerRankWeight]
  | @insert a s hmax ih =>
      have ha : a ∉ s := by
        intro ha
        exact (lt_irrefl a) (hmax a ha)
      have hfiltera :
          (insert a s).filter (fun i : ℤ => i < a) = s := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨hi | hi, hia⟩
          · subst i
            exact (lt_irrefl _ hia).elim
          · exact hi
        · intro hi
          exact ⟨Or.inr hi, hmax i hi⟩
      have hprefixa :
          lowerRankWeight (insert a s) w a = ∑ i ∈ s, w i := by
        unfold lowerRankWeight
        rw [hfiltera]
      have hprefix (j : ℤ) (hj : j ∈ s) :
          lowerRankWeight (insert a s) w j = lowerRankWeight s w j := by
        unfold lowerRankWeight
        have hnot : ¬ a < j := not_lt_of_ge (le_of_lt (hmax j hj))
        rw [Finset.filter_insert, if_neg hnot]
      calc
        (∑ j ∈ insert a s,
            w j * (lowerRankWeight (insert a s) w j + w j / 2) ^ 2) =
          w a * ((∑ i ∈ s, w i) + w a / 2) ^ 2 +
            ∑ j ∈ s, w j * (lowerRankWeight s w j + w j / 2) ^ 2 := by
              rw [Finset.sum_insert ha, hprefixa]
              congr 1
              apply Finset.sum_congr rfl
              intro j hj
              rw [hprefix j hj]
        _ = w a * ((∑ i ∈ s, w i) + w a / 2) ^ 2 +
            ((∑ j ∈ s, w j) ^ 3 / 3 -
              (∑ j ∈ s, w j ^ 3) / 12) := by rw [ih]
        _ = (∑ j ∈ insert a s, w j) ^ 3 / 3 -
            (∑ j ∈ insert a s, w j ^ 3) / 12 := by
              rw [Finset.sum_insert ha, Finset.sum_insert ha]
              ring
end SoficGroups.ComponentMidrankVariance
