-- Prove2me | solution 1 for P2M_GroundTheory_GroupCoh___apply_norm_cd75b4d7bf64
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:33:50.10545+00:00
-- url     : https://prove2.me/submissions/82e093d2-5bfc-4ad0-b634-50d9cc7ea918

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_DiagonalSuccIsoFreeInvSingle

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
open CategoryTheory Limits groupCohomology Rep
universe v w u
variable {k H : Type u} [CommRing k] [Group H] [Fintype H]
namespace GroundTheory.GroupCoh
theorem _root_.solution (B : Rep.{u} k H) (b : B) (s : H) : B.ρ s (B.ρ.norm b) = B.ρ.norm b := by
  rw [Representation.norm, LinearMap.sum_apply, map_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft s) _ _ fun t => ?_
  simp [← Module.End.mul_apply, ← map_mul]
end GroundTheory.GroupCoh
