-- Prove2me | solution 1 for P2M_GroundTheory_GroupCoh_indSES_map____b9067ca7808e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:15:08.946794+00:00
-- url     : https://prove2.me/submissions/94c3f7c6-4cab-47e1-91d8-23aca3fa2971

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
theorem _root_.solution {A B : Rep.{u} k G} (f : A ⟶ B) : (indSES.map f).τ₃ = f := rfl
end GroundTheory.GroupCoh
