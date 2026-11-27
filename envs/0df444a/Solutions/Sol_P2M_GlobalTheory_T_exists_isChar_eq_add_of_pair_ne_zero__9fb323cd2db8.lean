-- Prove2me | solution 1 for P2M_GlobalTheory_T_exists_isChar_eq_add_of_pair_ne_zero__9fb323cd2db8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:53:41.46077+00:00
-- url     : https://prove2.me/submissions/5e7031e5-8659-4919-870a-7e82dba78422

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsIsCharEqAddOfPairNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsIsCharEqAddOfPairNeZeroStatement
import Theorems.Thm_GlobalTheory_BI_exists_isChar_eq_add_of_pair_ne_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.BI
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L] (G : Type) [Group G] [Finite G] (φ a : G → L), IsIrrChar K L φ → IsChar K L a → pair a φ ≠ 0 → ∃ c : G → L, IsChar K L c ∧ a = φ + c := by
  first | exact @GlobalTheory.BI.exists_isChar_eq_add_of_pair_ne_zero | exact GlobalTheory.BI.exists_isChar_eq_add_of_pair_ne_zero | (intros; apply GlobalTheory.BI.exists_isChar_eq_add_of_pair_ne_zero <;> assumption)
end _root_.GlobalTheory.T
