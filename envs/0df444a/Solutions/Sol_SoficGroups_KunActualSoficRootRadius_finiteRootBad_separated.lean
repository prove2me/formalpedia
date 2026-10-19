-- Prove2me | solution 1 for SoficGroups.KunActualSoficRootRadius.finiteRootBad_separated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:57.599909+00:00
-- url     : https://prove2.me/submissions/e95202cf-76aa-4537-8781-f82d245e9a13

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
    {G : Type*} [Group G]
    (M : SoficGroups.PermutationModel G) (F : Finset G)
    {g h : G} (hg : g ∈ F) (hh : h ∈ F) (hne : g ≠ h)
    {x : Fin M.size} (hx : x ∉ finiteRootBad M F) :
    M.action g x ≠ M.action h x := by
  classical
  intro heq
  apply hx
  apply Finset.mem_union_right
  exact Finset.mem_biUnion.mpr
    ⟨(g, h), Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hg, hh⟩, hne⟩,
      (mem_modelSeparationBad M g h x).mpr heq⟩
end SoficGroups.KunActualSoficRootRadius
