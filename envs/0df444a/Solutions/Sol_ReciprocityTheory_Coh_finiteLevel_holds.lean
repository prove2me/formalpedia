-- Prove2me | solution 1 for ReciprocityTheory.Coh.finiteLevel_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:20:39.411408+00:00
-- url     : https://prove2.me/submissions/ffc2ce88-e53f-4c4a-abd4-57ce208ac60d

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_ResNormalHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_InfRes
import Definitions.Def_ReciprocityTheory_GroupCohomology_FiniteLevel
import Theorems.Thm_ReciprocityTheory_Coh_FiniteLevelCohomology_exists_level
import Theorems.Thm_ReciprocityTheory_Coh_FiniteLevelCohomology_torsion_finite
import Theorems.Thm_ReciprocityTheory_Coh_InflationRestrictionInvariants_invariants_isInvRep


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
open ReciprocityTheory.Gal Topology
open scoped Pointwise
universe u
namespace ReciprocityTheory.Coh
theorem _root_.solution : FiniteLevelStatement.{u} := by
  intro R _ G _ _ _ _ _ _ M _ n x
  obtain ⟨N, hN, hNo, hlev⟩ := FiniteLevelCohomology.exists_level M n x
  refine ⟨⟨N, hN, hNo, hlev⟩, fun hn => ?_⟩
  obtain ⟨y, hy⟩ := hlev _ _ (InflationRestrictionInvariants.invariants_isInvRep M N)
  haveI : DiscreteTopology (G ⧸ N) := QuotientGroup.discreteTopology hNo
  haveI : Finite (G ⧸ N) := Subgroup.quotient_finite_of_isOpen N hNo
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  refine ⟨Nat.card (G ⧸ N), Nat.card_pos, ?_⟩
  rw [← hy, ← map_nsmul, FiniteLevelCohomology.torsion_finite _ m y, map_zero]
end ReciprocityTheory.Coh
