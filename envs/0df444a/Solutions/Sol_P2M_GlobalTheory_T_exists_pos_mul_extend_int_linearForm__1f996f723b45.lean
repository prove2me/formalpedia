-- Prove2me | solution 1 for P2M_GlobalTheory_T_exists_pos_mul_extend_int_linearForm__1f996f723b45
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:52:46.68417+00:00
-- url     : https://prove2.me/submissions/104c91f2-b7a1-4c38-9717-affc65c6ac27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPosMulExtendIntLinearForm
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPosMulExtendIntLinearFormStatement
import Theorems.Thm_GlobalTheory_exists_pos_mul_extend_int_linearForm


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
theorem _root_.solution : ∀ (F : Type) [AddCommGroup F] [Module.Free ℤ F] [Module.Finite ℤ F] (P : Submodule ℤ F) (f : P →ₗ[ℤ] ℤ), ∃ c : ℤ, 0 < c ∧ ∃ lam : F →ₗ[ℤ] ℤ, ∀ x : P, lam x = c * f x := by
  first | exact @GlobalTheory.exists_pos_mul_extend_int_linearForm | exact GlobalTheory.exists_pos_mul_extend_int_linearForm | (intros; apply GlobalTheory.exists_pos_mul_extend_int_linearForm <;> assumption)
end _root_.GlobalTheory.T
