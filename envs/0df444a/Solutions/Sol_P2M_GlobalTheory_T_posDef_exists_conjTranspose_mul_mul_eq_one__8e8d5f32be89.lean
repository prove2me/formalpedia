-- Prove2me | solution 1 for P2M_GlobalTheory_T_posDef_exists_conjTranspose_mul_mul_eq_one__8e8d5f32be89
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:33:51.991784+00:00
-- url     : https://prove2.me/submissions/123d177a-a807-4e00-b9ae-10e5dcba70e4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PosDefExistsConjTransposeMulMulEqOne
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PosDefExistsConjTransposeMulMulEqOneStatement
import Theorems.Thm_GlobalTheory_posDef_exists_conjTranspose_mul_mul_eq_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ComplexOrder
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (d : ℕ) (H : Matrix (Fin d) (Fin d) ℂ), H.PosDef → ∃ y₀ : GL (Fin d) ℂ, (y₀.1).conjTranspose * H * y₀.1 = 1 := by
  first | exact @GlobalTheory.posDef_exists_conjTranspose_mul_mul_eq_one | exact GlobalTheory.posDef_exists_conjTranspose_mul_mul_eq_one | (intros; apply GlobalTheory.posDef_exists_conjTranspose_mul_mul_eq_one <;> assumption)
end _root_.GlobalTheory.T
