-- Prove2me | solution 1 for SoficGroups.KunAdditiveMedianPoincare.sum_indicator_real_eq_mul_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.855273+00:00
-- url     : https://prove2.me/submissions/94620474-87df-485d-a5ab-c343edf56d4b

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunAdditiveMedianPoincare
open SoficGroups.CheegerPoincare
open Filter Topology
open scoped BigOperators
namespace SoficGroups.KunAdditiveMedianPoincare
theorem _root_.solution
    {V : Type*} (A : Finset V)
    (q : V → Prop) [DecidablePred q] (m : ℝ) :
    (∑ x ∈ A, if q x then m else 0) =
      m * (A.filter q).card := by
  calc
    (∑ x ∈ A, if q x then m else 0) =
        m * (∑ x ∈ A, if q x then (1 : ℝ) else 0) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _
          split <;> simp
    _ = m * (A.filter q).card := by
          congr 1
          exact Finset.sum_boole (R := ℝ) q A
end SoficGroups.KunAdditiveMedianPoincare
