-- Prove2me | solution 1 for SoficGroups.KunActualSoficRootRadius.chosenFiniteMultiplicationBad_density_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:57.599909+00:00
-- url     : https://prove2.me/submissions/48f050c3-4e23-4a0f-9e82-f2aca6b91134

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_finite_union_bad_density_tendsto_zero
import Theorems.Thm_SoficGroups_KunActualSoficRootRadius_chosenWordMultiplicationBad_density_tendsto_zero

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
        ((chosenFiniteMultiplicationBad A s w F n).card : ℝ) /
          (A.model n).size)
      atTop (𝓝 0) := by
  classical
  have h := SoficGroups.finite_union_bad_density_tendsto_zero
    (F.product F)
    (fun n => (Finset.univ : Finset (Fin (A.model n).size)))
    (fun n (q : G × G) =>
      chosenWordMultiplicationBad A s w n q.1 q.2)
    (fun q _ => by
      simpa only [Finset.univ_inter, Finset.card_univ,
        Fintype.card_fin] using
        chosenWordMultiplicationBad_density_tendsto_zero
          A s w hw q.1 q.2)
  simpa only [chosenFiniteMultiplicationBad, Finset.univ_inter,
    Finset.card_univ, Fintype.card_fin] using h
end SoficGroups.KunActualSoficRootRadius
