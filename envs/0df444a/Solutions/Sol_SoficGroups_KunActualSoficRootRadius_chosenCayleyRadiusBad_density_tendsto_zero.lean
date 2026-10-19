-- Prove2me | solution 1 for SoficGroups.KunActualSoficRootRadius.chosenCayleyRadiusBad_density_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:57.599909+00:00
-- url     : https://prove2.me/submissions/4653ee6b-b9a3-4cd8-adef-a010001b7625

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunActualSoficRootRadius_chosenFiniteRootBad_density_tendsto_zero

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunActualSoficRootRadius
open Filter Topology
open scoped BigOperators Pointwise
namespace SoficGroups.KunActualSoficRootRadius
theorem _root_.solution
    {G : Type*} [Group G] [DecidableEq G]
    (A : SoficGroups.SoficApproximation G)
    (S : Finset G) (w : G → List ↥S)
    (hw : ∀ g, ((w g).map fun i : ↥S => (i : G)).prod = g)
    (r : ℕ) :
    Tendsto
      (fun n =>
        ((chosenCayleyRadiusBad A S w n r).card : ℝ) /
          (A.model n).size)
      atTop (𝓝 0) :=
  chosenFiniteRootBad_density_tendsto_zero
    A (fun i : ↥S => (i : G)) w hw (S ^ r)
end SoficGroups.KunActualSoficRootRadius
