-- Prove2me | solution 1 for P2M_GroundTheory_GroupCoh_TateAcyclic_of_shortExact_X__8e70e005e54b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:33:57.509378+00:00
-- url     : https://prove2.me/submissions/3fc9f2b6-0f77-4b39-8711-7db585b464c5

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
    (hS : S.ShortExact) (h₂ : TateAcyclic S.X₂) (h₁ : TateAcyclic S.X₁) : TateAcyclic S.X₃ :=
  fun n => (h₁ (n + 1)).of_iso
    (@asIso _ _ _ _ (TateCohomology.δ hS n) (isIso_δ_of_tateAcyclic hS h₂ n))
end TateAcyclic
end GroundTheory.GroupCoh
