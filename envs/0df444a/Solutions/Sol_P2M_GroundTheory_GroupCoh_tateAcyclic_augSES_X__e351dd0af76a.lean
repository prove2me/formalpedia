-- Prove2me | solution 1 for P2M_GroundTheory_GroupCoh_tateAcyclic_augSES_X__e351dd0af76a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:54:59.873797+00:00
-- url     : https://prove2.me/submissions/08273653-ffcf-448e-ac6d-59e67aea574f

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_InducedNorm
import Definitions.Def_GroundTheory_TateCohomology_DimensionShift
import Definitions.Def_GroundTheory_TateCohomology_TateConnecting
import Definitions.Def_GroundTheory_TateCohomology_AugmentationSES
import Theorems.Thm_GroundTheory_GroupCoh_tateAcyclic_leftRegular_tensor


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory MonoidalCategory
open GroundTheory GroundTheory.GroupCoh
universe u
variable {k G : Type u} [CommRing k] [Group G]
variable (k G)
variable {k G}
variable (k G)
variable {k G}
variable [Fintype G]
namespace GroundTheory.GroupCoh
theorem _root_.solution (X : Rep.{u} k G) : TateAcyclic ((augSES k G).obj X).X₂ :=
  tateAcyclic_leftRegular_tensor X
end GroundTheory.GroupCoh
