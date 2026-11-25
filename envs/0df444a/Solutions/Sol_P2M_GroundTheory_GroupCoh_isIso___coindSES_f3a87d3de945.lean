-- Prove2me | solution 1 for P2M_GroundTheory_GroupCoh_isIso___coindSES_f3a87d3de945
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:51:37.798855+00:00
-- url     : https://prove2.me/submissions/b8268bd9-35b8-4487-bc38-149aa13afb63

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
variable [Fintype G]
namespace GroundTheory.GroupCoh
theorem _root_.solution (A : Rep.{u} k G) (n : ℤ) :
    IsIso (TateCohomology.δ (coindSES_shortExact A) n) :=
  isIso_δ_of_tateAcyclic _ (tateAcyclic_coindSES_X₂ A) n
end GroundTheory.GroupCoh
