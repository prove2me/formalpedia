-- Prove2me | solution 1 for P2M_GroundTheory_GroupCoh_pullbackSESHom____538251148457
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:27:44.330037+00:00
-- url     : https://prove2.me/submissions/4e9079f8-d3db-42ad-8d91-c2a3b33e3d91

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
theorem _root_.solution : (pullbackSESHom S β).τ₃ = β := rfl
end GroundTheory.GroupCoh
