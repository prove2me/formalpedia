-- Prove2me | solution 1 for SoficGroups.KunActualSoficRootRadius.chosenWordEvaluation_tendsto_action
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:57.599909+00:00
-- url     : https://prove2.me/submissions/22b63c70-c903-462e-bc74-fa4332a51291

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunActualSoficRootRadius_action_list_prod_tendsto

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
    (hw : ∀ g, ((w g).map s).prod = g) (g : G) :
    Tendsto
      (fun n =>
        SoficGroups.normalizedHamming
          ((A.model n).action g)
          (chosenWordEvaluation A s w n g))
      atTop (𝓝 0) := by
  have h := action_list_prod_tendsto A ((w g).map s)
  simpa [chosenWordEvaluation, List.map_map,
    Function.comp_def, hw g] using h
end SoficGroups.KunActualSoficRootRadius
