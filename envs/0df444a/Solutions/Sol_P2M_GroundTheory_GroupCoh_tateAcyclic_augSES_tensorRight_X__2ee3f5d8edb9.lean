-- Prove2me | solution 1 for P2M_GroundTheory_GroupCoh_tateAcyclic_augSES_tensorRight_X__2ee3f5d8edb9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:09:48.217918+00:00
-- url     : https://prove2.me/submissions/9619dc50-415f-47bd-814e-95c8566e8e18

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_InducedNorm
import Definitions.Def_GroundTheory_TateCohomology_DimensionShift
import Definitions.Def_GroundTheory_TateCohomology_TateConnecting
import Definitions.Def_GroundTheory_TateCohomology_AugmentationSES
import Theorems.Thm_GroundTheory_GroupCoh_TateAcyclic_of_iso
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
theorem _root_.solution (A B : Rep.{u} k G) :
    TateAcyclic (((augSES k G).obj A).map (tensorRight B)).X₂ :=
  (tateAcyclic_leftRegular_tensor (A ⊗ B)).of_iso (α_ (Rep.leftRegular k G) A B)
end GroundTheory.GroupCoh
