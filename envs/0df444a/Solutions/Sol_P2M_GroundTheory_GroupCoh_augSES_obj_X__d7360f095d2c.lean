-- Prove2me | solution 1 for P2M_GroundTheory_GroupCoh_augSES_obj_X__d7360f095d2c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:33:59.013585+00:00
-- url     : https://prove2.me/submissions/7a6d18f6-8797-45fe-bcdb-da240cddd5b7

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_InducedNorm
import Definitions.Def_GroundTheory_TateCohomology_DimensionShift
import Definitions.Def_GroundTheory_TateCohomology_TateConnecting
import Definitions.Def_GroundTheory_TateCohomology_AugmentationSES

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
namespace GroundTheory.GroupCoh
theorem _root_.solution (X : Rep.{u} k G) :
    ((augSES k G).obj X).X₂ = Rep.leftRegular k G ⊗ X := rfl
end GroundTheory.GroupCoh
