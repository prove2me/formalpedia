-- Prove2me | solution 1 for P2M_GroundTheory_PAdicHodge_TeichLift_coeff___pow_mul_of_lt_398143255abf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:39:39.561397+00:00
-- url     : https://prove2.me/submissions/9d7ed8d3-01f4-40f5-89d2-fb242f4b8372

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaTeich
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_TeichLift_coeff___mul_succ_f7b410ef729e
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_TeichLift_coeff___mul_zero_c24e500c7aa0
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.TeichLift.coeff_π_mul_zero

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
theorem _root_.solution {k : ℕ} (x : Γ) {n : ℕ} (h : n < k) : T.coeff (T.π ^ k * x) n = 0 := by
  induction k generalizing n with
  | zero => omega
  | succ k ih =>
    rw [pow_succ', mul_assoc]
    rcases n with _ | n
    · exact T.coeff_π_mul_zero _
    · rw [coeff_π_mul_succ, ih (by omega)]
end GroundTheory.PAdicHodge.TeichLift
