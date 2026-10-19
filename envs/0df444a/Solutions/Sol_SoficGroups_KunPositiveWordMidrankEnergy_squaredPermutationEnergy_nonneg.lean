-- Prove2me | solution 1 for SoficGroups.KunPositiveWordMidrankEnergy.squaredPermutationEnergy_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.855273+00:00
-- url     : https://prove2.me/submissions/d2679002-c0ef-42af-b117-43e713b27894

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunPositiveWordMidrankEnergy
open Filter Topology
open scoped BigOperators
namespace SoficGroups.KunPositiveWordMidrankEnergy
theorem _root_.solution
    {V : Type*} [Fintype V] (f : V → ℝ) (p : Equiv.Perm V) :
    0 ≤ squaredPermutationEnergy f p := by
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _
end SoficGroups.KunPositiveWordMidrankEnergy
