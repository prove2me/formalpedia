-- Prove2me | solution 1 for SoficGroups.RankArcCharging.selectedRankSupport_rank_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.013021+00:00
-- url     : https://prove2.me/submissions/9de51963-4892-4444-b05e-e8e31e59a020

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
open SoficGroups.RankArcCharging
open scoped BigOperators
namespace SoficGroups.RankArcCharging
theorem _root_.solution
    {V : Type*} [DecidableEq V] {U : Finset V}
    (P : Finpartition U) (b : V → ℤ) (j : Finset V → ℤ)
    {x : V} (hx : x ∈ selectedRankSupport P b j) :
    b x = j (P.part x) := by
  obtain ⟨C, hC, hxC⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨hxmem, hxrank⟩ := Finset.mem_filter.mp hxC
  have hpart : P.part x = C := P.part_eq_of_mem hC hxmem
  simpa [hpart] using hxrank
end SoficGroups.RankArcCharging
