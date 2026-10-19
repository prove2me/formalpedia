-- Prove2me | solution 1 for SoficGroups.KunSharpThresholdCut.highCrossingProfile_eq_boundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.059963+00:00
-- url     : https://prove2.me/submissions/3dad33c8-6ca9-48d1-b328-d30d9b602b43

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunSharpThresholdCut
open MeasureTheory Set
open scoped BigOperators ENNReal symmDiff
namespace SoficGroups.KunSharpThresholdCut
theorem _root_.solution {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (f : V → ℝ) (a t : ℝ)
    (hat : a < t) :
    highCrossingProfile σ f a t =
      (SoficGroups.boundary σ (upperLevel f t) : ℝ) := by
  classical
  unfold highCrossingProfile SoficGroups.boundary upperLevel
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.card_eq_sum_ones]
  push_cast
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x _
  simp only [mem_Ico, indicator,
    Finset.mem_filter, Finset.mem_univ, true_and]
  split_ifs
  all_goals grind
end SoficGroups.KunSharpThresholdCut
