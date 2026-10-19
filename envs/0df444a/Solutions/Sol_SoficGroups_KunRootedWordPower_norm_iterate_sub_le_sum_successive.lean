-- Prove2me | solution 1 for SoficGroups.KunRootedWordPower.norm_iterate_sub_le_sum_successive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.059963+00:00
-- url     : https://prove2.me/submissions/c0d7502f-ab59-47d6-9378-d289ad2cbe00

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunRootedWordPower
open Filter Topology
open SoficGroups.KunRootedIndicatorCrossing
open SoficGroups.KunThomInvariantOrthogonal
open scoped BigOperators ComplexConjugate ComplexOrder InnerProductSpace Pointwise
universe u v
namespace SoficGroups.KunRootedWordPower
theorem _root_.solution
    {E : Type*} [NormedAddCommGroup E]
    (F : E → E) (x : E) (k : ℕ) :
    ‖(F^[k]) x - x‖ ≤
      ∑ j ∈ Finset.range k,
        ‖(F^[j + 1]) x - (F^[j]) x‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ]
      calc
        ‖(F^[k + 1]) x - x‖ =
            ‖((F^[k]) x - x) +
              ((F^[k + 1]) x - (F^[k]) x)‖ := by
              congr 1
              abel
        _ ≤ ‖(F^[k]) x - x‖ +
              ‖(F^[k + 1]) x - (F^[k]) x‖ :=
          norm_add_le _ _
        _ ≤ (∑ j ∈ Finset.range k,
              ‖(F^[j + 1]) x - (F^[j]) x‖) +
              ‖(F^[k + 1]) x - (F^[k]) x‖ :=
          add_le_add ih (le_refl _)
end SoficGroups.KunRootedWordPower
