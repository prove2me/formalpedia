-- Prove2me | solution 1 for P2M_GroundTheory_PAdicHodge_TeichLift_exists_add___mul_pow_sub_5a50fafd6f50
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:59:31.722931+00:00
-- url     : https://prove2.me/submissions/fa651648-5d5e-46f7-8c02-958b083daf0f

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaTeich
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_coeff_ofCoeff
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_TeichLift_coeff___mul_zero_c24e500c7aa0
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_coeff_zero_elem
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_exists_pow_sub_pow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.TeichLift.coeff_ofCoeff
attribute [local simp] GroundTheory.PAdicHodge.TeichLift.coeff_π_mul_zero
attribute [local simp] GroundTheory.PAdicHodge.TeichLift.coeff_zero_elem

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
theorem _root_.solution (A z : Γ) (hA : A ∈ T.int) (hz : z ∈ T.int) (k : ℕ) :
    ∃ w ∈ T.int, (A + T.π * z) ^ p ^ k - A ^ p ^ k = T.π ^ (k + 1) * w := by
  induction k with
  | zero => exact ⟨z, hz, by simp⟩
  | succ k ih =>
    obtain ⟨w, hw, h⟩ := ih
    rw [pow_succ, pow_mul, pow_mul]
    exact T.exists_pow_sub_pow (pow_mem (add_mem hA (mul_mem T.π_mem_int hz)) _) (pow_mem hA _) hw
      (by omega) h
end GroundTheory.PAdicHodge.TeichLift
