-- Prove2me | solution 1 for P2M_GroundTheory_PAdicHodge_TeichLift_finSum_succ__591efcd7936f
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:35:37.532803+00:00
-- url     : https://prove2.me/submissions/76d6446a-d0d8-45e3-8a4e-38bd6237122d

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
theorem _root_.solution (a : ℕ → L) (n : ℕ) :
    T.finSum a (n + 1) = T.teich (a 0) + T.π * T.finSum (fun i => a (i + 1)) n := by
  simp only [finSum, Finset.sum_range_succ', pow_zero, one_mul, Finset.mul_sum]
  rw [add_comm]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  ring
end GroundTheory.PAdicHodge.TeichLift
