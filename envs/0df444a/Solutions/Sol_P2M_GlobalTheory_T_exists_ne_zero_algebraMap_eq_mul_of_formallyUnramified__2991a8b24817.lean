-- Prove2me | solution 1 for P2M_GlobalTheory_T_exists_ne_zero_algebraMap_eq_mul_of_formallyUnramified__2991a8b24817
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:33:50.041982+00:00
-- url     : https://prove2.me/submissions/5359faf4-7165-499c-9b3f-7daa0a22b084

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsNeZeroAlgebraMapEqMulOfFormallyUnramifiedA
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsNeZeroAlgebraMapEqMulOfFormallyUnramifiedAStatement
import Theorems.Thm_GlobalTheory_exists_ne_zero_algebraMap_eq_mul_of_formallyUnramified


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (P D : Type) [CommRing P] [IsDomain P] [CommRing D] [IsDomain D] [Algebra P D] [Algebra.FiniteType P D] [Algebra.FormallyUnramified P D] (f : D), f ≠ 0 → ∃ Q : P, Q ≠ 0 ∧ ∃ d : D, algebraMap P D Q = f * d := by
  first | exact @GlobalTheory.exists_ne_zero_algebraMap_eq_mul_of_formallyUnramified | exact GlobalTheory.exists_ne_zero_algebraMap_eq_mul_of_formallyUnramified | (intros; apply GlobalTheory.exists_ne_zero_algebraMap_eq_mul_of_formallyUnramified <;> assumption)
end _root_.GlobalTheory.T
