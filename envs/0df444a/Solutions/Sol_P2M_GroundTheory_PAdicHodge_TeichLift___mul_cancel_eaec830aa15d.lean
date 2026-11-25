-- Prove2me | solution 1 for P2M_GroundTheory_PAdicHodge_TeichLift___mul_cancel_eaec830aa15d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:50:36.194958+00:00
-- url     : https://prove2.me/submissions/e2ac5d60-1311-4105-aadb-3c19249cc119

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaTeich
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_TeichLift___pow_mul_cancel_0b74b6c14644

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
theorem _root_.solution {x y : Γ} (h : T.π * x = T.π * y) : x = y :=
  T.π_pow_mul_cancel (n := 1) (by simpa using h)
end GroundTheory.PAdicHodge.TeichLift
