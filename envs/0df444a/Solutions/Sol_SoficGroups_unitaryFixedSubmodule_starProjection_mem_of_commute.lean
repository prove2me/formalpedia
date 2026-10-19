-- Prove2me | solution 1 for SoficGroups.unitaryFixedSubmodule_starProjection_mem_of_commute
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:54.580336+00:00
-- url     : https://prove2.me/submissions/129f709a-ffb7-421d-84fd-45588fd00630

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_unitaryFixedSubmodule_starProjection_commute

set_option autoImplicit true
noncomputable section
open SoficGroups
open scoped BigOperators commutatorElement
universe u₁ v₁
namespace SoficGroups
theorem _root_.solution
    {G : Type u₁} {H : Type v₁} [Group G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : UnitaryRepresentation G H) (K J : Subgroup G)
    (hcomm : ∀ k : K, ∀ j : J, Commute (k : G) (j : G))
    {x : H} (hx : x ∈ unitaryFixedSubmodule π J) :
    (unitaryFixedSubmodule π K).starProjection x ∈
      unitaryFixedSubmodule π J := by
  letI : CompleteSpace (unitaryFixedSubmodule π K) :=
    unitaryFixedSubmodule_completeSpace π K
  rw [mem_unitaryFixedSubmodule]
  intro j
  have hj := (mem_unitaryFixedSubmodule π J x).mp hx j
  have he := unitaryFixedSubmodule_starProjection_commute π K (j : G)
    (fun k => (hcomm k j).symm) x
  simpa [hj] using he.symm
end SoficGroups
