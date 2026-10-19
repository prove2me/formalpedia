-- Prove2me | solution 1 for SoficGroups.KunActualSoficRootRadius.finiteRootBad_density_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:57.599909+00:00
-- url     : https://prove2.me/submissions/653deb7a-c3c8-47db-a209-c42643638b76

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunActualSoficRootRadius_finiteMultiplicationBad_density_tendsto_zero
import Theorems.Thm_SoficGroups_KunActualSoficRootRadius_finiteSeparationBad_density_tendsto_zero

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunActualSoficRootRadius
open Filter Topology
open scoped BigOperators Pointwise
namespace SoficGroups.KunActualSoficRootRadius
theorem _root_.solution
    {G : Type*} [Group G]
    (A : SoficGroups.SoficApproximation G) (F : Finset G) :
    Tendsto
      (fun n =>
        ((finiteRootBad (A.model n) F).card : ℝ) /
          (A.model n).size)
      atTop (𝓝 0) := by
  have hsum :
      Tendsto
        (fun n =>
          ((finiteMultiplicationBad (A.model n) F).card : ℝ) /
              (A.model n).size +
            ((finiteSeparationBad (A.model n) F).card : ℝ) /
              (A.model n).size)
        atTop (𝓝 0) := by
    simpa using
      (finiteMultiplicationBad_density_tendsto_zero A F).add
        (finiteSeparationBad_density_tendsto_zero A F)
  refine squeeze_zero (fun n => by positivity) ?_ hsum
  intro n
  have hcard :
      ((finiteRootBad (A.model n) F).card : ℝ) ≤
        (finiteMultiplicationBad (A.model n) F).card +
          (finiteSeparationBad (A.model n) F).card := by
    exact_mod_cast Finset.card_union_le
      (finiteMultiplicationBad (A.model n) F)
      (finiteSeparationBad (A.model n) F)
  calc
    ((finiteRootBad (A.model n) F).card : ℝ) /
        (A.model n).size ≤
      (((finiteMultiplicationBad (A.model n) F).card : ℝ) +
        (finiteSeparationBad (A.model n) F).card) /
          (A.model n).size :=
        div_le_div_of_nonneg_right hcard (by positivity)
    _ = ((finiteMultiplicationBad (A.model n) F).card : ℝ) /
          (A.model n).size +
        ((finiteSeparationBad (A.model n) F).card : ℝ) /
          (A.model n).size := by
        rw [add_div]
end SoficGroups.KunActualSoficRootRadius
