-- Prove2me | solution 1 for P2M_GroundTheory_GroupCoh_indSES_obj_X__e6c60d2b2881
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:14:54.357231+00:00
-- url     : https://prove2.me/submissions/57a34b71-1a34-4624-ac98-21cc550f3178

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_Induced
import Definitions.Def_GroundTheory_TateCohomology_InducedNorm
import Definitions.Def_GroundTheory_TateCohomology_DimensionShift

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
variable {k G : Type u} [CommRing k] [Group G]
namespace GroundTheory.GroupCoh
theorem _root_.solution (A : Rep.{u} k G) :
    (indSES.obj A).X₂ = ind (⊥ : Subgroup G).subtype (res (⊥ : Subgroup G).subtype A) := rfl
end GroundTheory.GroupCoh
