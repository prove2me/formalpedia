-- Prove2me | solution 1 for SoficGroups.KunActualSoficRootRadius.finiteRootBad_multiplicative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:57.599909+00:00
-- url     : https://prove2.me/submissions/35ac4d83-27ce-4c0e-a050-0c064b3180fb

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
    {g h : G} (hg : g ∈ F) (hh : h ∈ F)
    {x : Fin M.size} (hx : x ∉ finiteRootBad M F) :
    M.action (g * h) x = (M.action g * M.action h) x := by
  classical
  have hnot : x ∉ modelMultiplicationBad M g h := by
    intro hbad
    apply hx
    apply Finset.mem_union_left
    exact Finset.mem_biUnion.mpr
      ⟨(g, h), Finset.mem_product.mpr ⟨hg, hh⟩, hbad⟩
  simpa using hnot
end SoficGroups.KunActualSoficRootRadius
