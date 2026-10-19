-- Prove2me | solution 1 for SoficGroups.KunActualSoficRootRadius.chosenFiniteRootBad_density_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:57.599909+00:00
-- url     : https://prove2.me/submissions/02ee859a-6f5f-4810-9ead-4331b0f1925b

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunActualSoficRootRadius_finiteRootBad_density_tendsto_zero
import Theorems.Thm_SoficGroups_KunActualSoficRootRadius_chosenFiniteMultiplicationBad_density_tendsto_zero

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunActualSoficRootRadius
open Filter Topology
open scoped BigOperators Pointwise
namespace SoficGroups.KunActualSoficRootRadius
theorem _root_.solution
    {G ι : Type*} [Group G]
    (A : SoficGroups.SoficApproximation G)
    (s : ι → G) (w : G → List ι)
    (hw : ∀ g, ((w g).map s).prod = g) (F : Finset G) :
    Tendsto
      (fun n =>
        ((chosenFiniteRootBad A s w F n).card : ℝ) /
          (A.model n).size)
      atTop (𝓝 0) := by
  have hsum :
      Tendsto
        (fun n =>
          ((finiteRootBad (A.model n) F).card : ℝ) /
              (A.model n).size +
            ((chosenFiniteMultiplicationBad A s w F n).card : ℝ) /
              (A.model n).size)
        atTop (𝓝 0) := by
    simpa using
      (finiteRootBad_density_tendsto_zero A F).add
        (chosenFiniteMultiplicationBad_density_tendsto_zero
          A s w hw F)
  refine squeeze_zero (fun n => by positivity) ?_ hsum
  intro n
  have hcard :
      ((chosenFiniteRootBad A s w F n).card : ℝ) ≤
        (finiteRootBad (A.model n) F).card +
          (chosenFiniteMultiplicationBad A s w F n).card := by
    exact_mod_cast Finset.card_union_le
      (finiteRootBad (A.model n) F)
      (chosenFiniteMultiplicationBad A s w F n)
  calc
    ((chosenFiniteRootBad A s w F n).card : ℝ) /
        (A.model n).size ≤
      (((finiteRootBad (A.model n) F).card : ℝ) +
        (chosenFiniteMultiplicationBad A s w F n).card) /
          (A.model n).size :=
        div_le_div_of_nonneg_right hcard (by positivity)
    _ = ((finiteRootBad (A.model n) F).card : ℝ) /
          (A.model n).size +
        ((chosenFiniteMultiplicationBad A s w F n).card : ℝ) /
          (A.model n).size := by
        rw [add_div]
end SoficGroups.KunActualSoficRootRadius
