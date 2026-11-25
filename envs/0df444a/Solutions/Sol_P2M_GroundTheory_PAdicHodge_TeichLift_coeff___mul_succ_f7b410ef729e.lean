-- Prove2me | solution 1 for P2M_GroundTheory_PAdicHodge_TeichLift_coeff___mul_succ_f7b410ef729e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:36:10.116907+00:00
-- url     : https://prove2.me/submissions/7c532c95-a6f0-4d1e-8ac3-6f4a96d87ce7

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaTeich
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_tail_eq
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_coeff_succ
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_coeff_ofCoeff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.TeichLift.coeff_ofCoeff

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
theorem _root_.solution (x : Γ) (n : ℕ) : T.coeff (T.π * x) (n + 1) = T.coeff x n := by
  rw [coeff_succ, T.tail_eq (a := 0) (y := x) (by simp)]
end GroundTheory.PAdicHodge.TeichLift
