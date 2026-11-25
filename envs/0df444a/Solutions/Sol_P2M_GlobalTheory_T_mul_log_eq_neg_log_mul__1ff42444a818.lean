-- Prove2me | solution 1 for P2M_GlobalTheory_T_mul_log_eq_neg_log_mul__1ff42444a818
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:34:18.98161+00:00
-- url     : https://prove2.me/submissions/7a8854fb-c7ac-440c-a8b0-0f8dfd2ef184

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_MulLogEqNegLogMul
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_MulLogEqNegLogMulStatement
import Theorems.Thm_GlobalTheory_ClassFin_mul_log_eq_neg_log_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (x x' H H' : Matrix ι ι ℂ), IsLog H (xᴴ * x) → IsLog H' (x'ᴴ * x') → x' * x = 1 → x * H = -(H' * x) := by
  first | exact @GlobalTheory.ClassFin.mul_log_eq_neg_log_mul | exact GlobalTheory.ClassFin.mul_log_eq_neg_log_mul | (intros; apply GlobalTheory.ClassFin.mul_log_eq_neg_log_mul <;> assumption)
end _root_.GlobalTheory.T
