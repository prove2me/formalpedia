-- Prove2me | solution 1 for P2M_GroundTheory_GroupCoh_tateAcyclic_res_coindSES_X__44aff45c1b5f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:07:30.34084+00:00
-- url     : https://prove2.me/submissions/9962de34-dd8f-487e-96f4-f176f9cfbb3b

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CohTrivialBasic
import Definitions.Def_GroundTheory_TateCohomology_DimensionShift
import Definitions.Def_GroundTheory_TateCohomology_TateUnique
import Theorems.Thm_GroundTheory_GroupCoh_cohTrivial_coind_bot


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
universe u
variable {k G : Type u} [CommRing k] [Group G] [Fintype G]
namespace GroundTheory.GroupCoh
theorem _root_.solution (U : Subgroup G) [Fintype U] (A : Rep.{u} k G) :
    TateAcyclic ((resFunctor U.subtype).obj (coindSES.obj A).X₂) :=
  cohTrivial_coind_bot _ U
end GroundTheory.GroupCoh
