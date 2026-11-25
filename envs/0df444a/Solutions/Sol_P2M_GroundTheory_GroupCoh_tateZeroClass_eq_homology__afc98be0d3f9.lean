-- Prove2me | solution 1 for P2M_GroundTheory_GroupCoh_tateZeroClass_eq_homology__afc98be0d3f9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:53:06.530328+00:00
-- url     : https://prove2.me/submissions/022318dc-5d50-44a4-b2fe-6596c0e8a7d9

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_TateLow
import Definitions.Def_GroundTheory_TateCohomology_TateZeroClass
import Theorems.Thm_GroundTheory_GroupCoh_tateCohomologyZeroIso_inv_mk


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
open CategoryTheory Limits Rep groupCohomology
universe u
variable {k G : Type u} [CommRing k] [Group G] [Fintype G]
namespace GroundTheory.GroupCoh
theorem _root_.solution (M : Rep.{u} k G) (z : (tateComplex M).cycles 0)
    (x : M.ρ.invariants) (hx : (cochainsIso₀ M).inv.hom x = ((tateComplex M).iCycles 0).hom z) :
    tateZeroClass M x = ((tateComplex M).homologyπ 0).hom z :=
  tateCohomologyZeroIso_inv_mk M z x hx
end GroundTheory.GroupCoh
