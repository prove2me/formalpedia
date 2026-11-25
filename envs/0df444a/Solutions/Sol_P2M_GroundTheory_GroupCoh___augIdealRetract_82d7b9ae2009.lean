-- Prove2me | solution 1 for P2M_GroundTheory_GroupCoh___augIdealRetract_82d7b9ae2009
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:09:43.330444+00:00
-- url     : https://prove2.me/submissions/c7b49229-bdec-48a7-a703-cacb83a57477

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
theorem _root_.solution (x : (Rep.leftRegular k G).V) :
    ((augIdealι k G).hom (augIdealRetract k G x)) =
      x - MonoidAlgebra.single 1 (augmentation k G x) := rfl
end GroundTheory.GroupCoh
