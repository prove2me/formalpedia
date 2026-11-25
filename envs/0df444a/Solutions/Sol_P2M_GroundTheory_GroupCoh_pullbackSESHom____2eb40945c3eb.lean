-- Prove2me | solution 1 for P2M_GroundTheory_GroupCoh_pullbackSESHom____2eb40945c3eb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:01:49.743875+00:00
-- url     : https://prove2.me/submissions/d6d967d1-0eaa-4726-8e3f-0c05e71b71eb

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_AugmentationSES
import Definitions.Def_GroundTheory_TateCohomology_PullbackExtension

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory
open GroundTheory GroundTheory.GroupCoh
universe u
variable {k G : Type u} [CommRing k] [Group G]
variable (S : ShortComplex (Rep.{u} k G)) {Y : Rep.{u} k G} (β : Y ⟶ S.X₃)
namespace GroundTheory.GroupCoh
theorem _root_.solution : (pullbackSESHom S β).τ₂ = pullbackFst S β := rfl
end GroundTheory.GroupCoh
