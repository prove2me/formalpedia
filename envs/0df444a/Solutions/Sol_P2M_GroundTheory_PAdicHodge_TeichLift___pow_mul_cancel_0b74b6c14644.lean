-- Prove2me | solution 1 for P2M_GroundTheory_PAdicHodge_TeichLift___pow_mul_cancel_0b74b6c14644
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:44:22.530558+00:00
-- url     : https://prove2.me/submissions/444eb38f-c41e-4e76-9a23-ffafebc4d4ba

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaTeich

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
open GroundTheory GroundTheory.PAdicHodge
open Ideal
open GroundTheory.PAdicHodge.TeichLift
variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] [CharP L p]
  [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)
namespace GroundTheory.PAdicHodge.TeichLift
theorem _root_.solution {n : ℕ} {x y : Γ} (h : T.π ^ n * x = T.π ^ n * y) : x = y := by
  have hπ := pow_mem T.π_mem_nonZeroDivisors n
  have : T.π ^ n * (x - y) = 0 := by rw [mul_sub, h, sub_self]
  exact sub_eq_zero.1 ((mem_nonZeroDivisors_iff.1 hπ).1 _ this)
end GroundTheory.PAdicHodge.TeichLift
