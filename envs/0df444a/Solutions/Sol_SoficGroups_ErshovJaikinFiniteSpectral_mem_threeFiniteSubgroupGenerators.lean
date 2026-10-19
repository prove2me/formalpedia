-- Prove2me | solution 1 for SoficGroups.ErshovJaikinFiniteSpectral.mem_threeFiniteSubgroupGenerators
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:54.580336+00:00
-- url     : https://prove2.me/submissions/a41b5b9c-332e-41ba-a65f-1bd9c4ad22b9

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.ErshovJaikinFiniteSpectral
open Filter Topology
universe u v
namespace SoficGroups.ErshovJaikinFiniteSpectral
theorem _root_.solution
    {G : Type u} [Group G] (K : Fin 3 → Subgroup G)
    [∀ i, Fintype (K i)] (g : G) :
    g ∈ threeFiniteSubgroupGenerators K ↔ ∃ i : Fin 3, g ∈ K i := by
  classical
  simp [threeFiniteSubgroupGenerators]
end SoficGroups.ErshovJaikinFiniteSpectral
