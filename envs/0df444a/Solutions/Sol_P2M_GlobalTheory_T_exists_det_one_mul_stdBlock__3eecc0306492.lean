-- Prove2me | solution 1 for P2M_GlobalTheory_T_exists_det_one_mul_stdBlock__3eecc0306492
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:52:03.528051+00:00
-- url     : https://prove2.me/submissions/a816adbc-3338-442d-9ea7-17e3551be9a6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDetOneMulStdBlock
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDetOneMulStdBlockStatement
import Theorems.Thm_GlobalTheory_exists_det_one_mul_stdBlock


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
theorem _root_.solution : ∀ {K : Type} [Field K] {n r : ℕ}, r < n → ∀ y : Matrix (Fin n) (Fin r) K, y.rank = r → ∃ g : GL (Fin n) K, Matrix.GeneralLinearGroup.det g = 1 ∧ g.val * (Matrix.of fun (a : Fin n) (b : Fin r) => if (a : ℕ) = (b : ℕ) then (1 : K) else 0) = y := by
  first | exact @GlobalTheory.exists_det_one_mul_stdBlock | exact GlobalTheory.exists_det_one_mul_stdBlock | (intros; apply GlobalTheory.exists_det_one_mul_stdBlock <;> assumption)
end _root_.GlobalTheory.T
