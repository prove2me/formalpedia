-- Prove2me | solution 1 for SoficGroups.KunDirectedIndicatorJensen.realPermutationMarkov_indicator_defect_sq_le_boundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:57.599909+00:00
-- url     : https://prove2.me/submissions/75ac9c11-e761-4915-97aa-258aa6545085

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunDirectedIndicatorJensen_sum_sum_sq_realIndicator_inverse_displacement
import Theorems.Thm_SoficGroups_KunDirectedIndicatorJensen_realPermutationMarkov_sub_sq_le_average_sq

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunDirectedIndicatorJensen
open scoped BigOperators
namespace SoficGroups.KunDirectedIndicatorJensen
theorem _root_.solution
    {V ι : Type*} [Fintype V] [DecidableEq V]
    [Fintype ι] [Nonempty ι]
    (σ : ι → Equiv.Perm V) (T : Finset V) :
    (∑ x : V,
      (realPermutationMarkov σ (realIndicator T) x -
        realIndicator T x) ^ 2) ≤
      2 * (SoficGroups.boundary σ T : ℝ) /
        (Fintype.card ι : ℝ) := by
  classical
  calc
    (∑ x : V,
      (realPermutationMarkov σ (realIndicator T) x -
        realIndicator T x) ^ 2) ≤
      ∑ x : V,
        (∑ i : ι,
          (realIndicator T ((σ i).symm x) -
            realIndicator T x) ^ 2) / (Fintype.card ι : ℝ) := by
          apply Finset.sum_le_sum
          intro x _
          exact realPermutationMarkov_sub_sq_le_average_sq
            σ (realIndicator T) x
    _ = (∑ i : ι, ∑ x : V,
          (realIndicator T ((σ i).symm x) -
            realIndicator T x) ^ 2) / (Fintype.card ι : ℝ) := by
          rw [← Finset.sum_div, Finset.sum_comm]
    _ = 2 * (SoficGroups.boundary σ T : ℝ) /
          (Fintype.card ι : ℝ) := by
          rw [sum_sum_sq_realIndicator_inverse_displacement]
end SoficGroups.KunDirectedIndicatorJensen
