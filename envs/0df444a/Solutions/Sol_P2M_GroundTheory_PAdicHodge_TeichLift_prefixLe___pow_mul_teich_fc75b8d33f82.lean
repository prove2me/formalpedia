-- Prove2me | solution 1 for P2M_GroundTheory_PAdicHodge_TeichLift_prefixLe___pow_mul_teich_fc75b8d33f82
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:18:16.537433+00:00
-- url     : https://prove2.me/submissions/c69c6e37-5e7b-431d-940a-9a00f6d58f9b

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaTeich
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_coeff_ofCoeff
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_TeichLift_coeff___mul_zero_c24e500c7aa0
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_coeff_zero_elem
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_TeichLift_coeff___pow_mul_teich_43d14c6acc24
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
theorem _root_.solution (k : ℕ) (c : L) (n : ℕ) {b : ℝ} (hb : 0 ≤ b)
    (h : k ≤ n → ‖c‖ ≤ b) : T.PrefixLe (T.π ^ k * T.teich c) n b := by
  intro m hm
  rw [coeff_π_pow_mul_teich]
  split_ifs with h'
  · subst h'; exact h hm
  · simpa using hb
end GroundTheory.PAdicHodge.TeichLift
