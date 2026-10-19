-- Prove2me | solution 1 for SoficGroups.KunActualSoficRootRadius.finiteMultiplicationBad_density_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:57.599909+00:00
-- url     : https://prove2.me/submissions/18388faa-1d48-47ed-888f-96575b9ee717

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_finite_union_bad_density_tendsto_zero
import Theorems.Thm_SoficGroups_KunActualSoficRootRadius_modelMultiplicationBad_density_tendsto_zero

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
        ((finiteMultiplicationBad (A.model n) F).card : ℝ) /
          (A.model n).size)
      atTop (𝓝 0) := by
  classical
  have h := SoficGroups.finite_union_bad_density_tendsto_zero
    (F.product F)
    (fun n => (Finset.univ : Finset (Fin (A.model n).size)))
    (fun n (q : G × G) =>
      modelMultiplicationBad (A.model n) q.1 q.2)
    (fun q _ => by
      simpa only [Finset.univ_inter, Finset.card_univ,
        Fintype.card_fin] using
        modelMultiplicationBad_density_tendsto_zero A q.1 q.2)
  simpa only [finiteMultiplicationBad, Finset.univ_inter,
    Finset.card_univ, Fintype.card_fin] using h
end SoficGroups.KunActualSoficRootRadius
