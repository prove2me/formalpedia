-- Prove2me | solution 1 for P2M_GroundTheory_PAdicHodge_TeichLift_coeff___pow_mul_teich_43d14c6acc24
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:13:08.707275+00:00
-- url     : https://prove2.me/submissions/87efb1bb-4ed6-4375-8403-d168baf49c88

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaTeich
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_TeichLift_coeff___pow_mul_add_de69595147c6
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_TeichLift_coeff___pow_mul_of_lt_398143255abf
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_coeff_teich

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
theorem _root_.solution (k : ℕ) (c : L) (n : ℕ) :
    T.coeff (T.π ^ k * T.teich c) n = if n = k then c else 0 := by
  rcases lt_or_ge n k with h | h
  · rw [T.coeff_π_pow_mul_of_lt _ h, if_neg (by omega)]
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' h
    rw [T.coeff_π_pow_mul_add, coeff_teich]
    split_ifs <;> first | rfl | omega
end GroundTheory.PAdicHodge.TeichLift
