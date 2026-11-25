-- Prove2me | solution 1 for P2M_GlobalTheory_T_exists_prime_not_mem_forall_gt_eq_maximalIdeal__e41b815ea9d1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:34:00.381165+00:00
-- url     : https://prove2.me/submissions/fa6744e1-fa13-4dd8-9376-dc58f0fd0b57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPrimeNotMemForallGtEqMaximalIdeal
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPrimeNotMemForallGtEqMaximalIdealStatement
import Theorems.Thm_GlobalTheory_exists_prime_not_mem_forall_gt_eq_maximalIdeal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (C : Type) [CommRing C] [IsDomain C] [IsLocalRing C] [IsNoetherianRing C] (x : C), x ≠ 0 → x ∈ maximalIdeal C → ∃ q : Ideal C, q.IsPrime ∧ x ∉ q ∧ ∀ P : Ideal C, P.IsPrime → q < P → P = maximalIdeal C := by
  first | exact @GlobalTheory.exists_prime_not_mem_forall_gt_eq_maximalIdeal | exact GlobalTheory.exists_prime_not_mem_forall_gt_eq_maximalIdeal | (intros; apply GlobalTheory.exists_prime_not_mem_forall_gt_eq_maximalIdeal <;> assumption)
end _root_.GlobalTheory.T
