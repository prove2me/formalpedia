-- Prove2me | solution 1 for P2M_GroundTheory_GroupCoh_TateAcyclic_of_shortExact_X__c00637e206cb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:34:03.342291+00:00
-- url     : https://prove2.me/submissions/e7fa160d-3a6a-4321-b26d-deb1048c151e

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_DimensionShift
import Definitions.Def_GroundTheory_TateCohomology_InducedNorm
import Definitions.Def_GroundTheory_TateCohomology_CoindOne
import Definitions.Def_GroundTheory_TateCohomology_UniquelyDivisible
import Definitions.Def_GroundTheory_TateCohomology_CohTrivialBasic
import Theorems.Thm_GroundTheory_GroupCoh_CohTrivial_of_iso
import Theorems.Thm_GroundTheory_GroupCoh_TateAcyclic_of_iso


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.GroupCoh
open CategoryTheory Limits Rep
open scoped MonoidAlgebra
universe u
variable {k G : Type u} [CommRing k] [Group G]
namespace GroundTheory.GroupCoh
namespace TateAcyclic
theorem _root_.solution [Fintype G] {S : ShortComplex (Rep.{u} k G)}
    (hS : S.ShortExact) (h₂ : TateAcyclic S.X₂) (h₃ : TateAcyclic S.X₃) : TateAcyclic S.X₁ :=
  fun n => by
    have e := @asIso _ _ _ _ (TateCohomology.δ hS (n - 1)) (isIso_δ_of_tateAcyclic hS h₂ (n - 1))
    have h := (h₃ (n - 1)).of_iso e.symm
    rwa [sub_add_cancel] at h
end TateAcyclic
end GroundTheory.GroupCoh
