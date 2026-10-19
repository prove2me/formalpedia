-- Prove2me | solution 1 for SoficGroups.KunActualSoficRootRadius.chosenFiniteMultiplicationBad_rooted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:57.599909+00:00
-- url     : https://prove2.me/submissions/cbe87150-91a8-414a-ac8f-d19dbc973dd0

import Mathlib
import Definitions.Def_NonSoficGroup

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
    (F : Finset G) (n : ℕ)
    {g h : G} (hg : g ∈ F) (hh : h ∈ F)
    {x : Fin (A.model n).size}
    (hx : x ∉ chosenFiniteMultiplicationBad A s w F n) :
    chosenWordEvaluation A s w n (g * h) x =
      (chosenWordEvaluation A s w n g *
        chosenWordEvaluation A s w n h) x := by
  classical
  have hnot : x ∉ chosenWordMultiplicationBad A s w n g h := by
    intro hbad
    apply hx
    exact Finset.mem_biUnion.mpr
      ⟨(g, h), Finset.mem_product.mpr ⟨hg, hh⟩, hbad⟩
  simpa using hnot
end SoficGroups.KunActualSoficRootRadius
