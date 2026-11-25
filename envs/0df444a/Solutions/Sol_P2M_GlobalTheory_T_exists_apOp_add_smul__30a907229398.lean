-- Prove2me | solution 1 for P2M_GlobalTheory_T_exists_apOp_add_smul__30a907229398
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:34:02.636521+00:00
-- url     : https://prove2.me/submissions/e9b713fd-85eb-4929-92eb-e839f5768b3d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsApOpAddSmul
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsApOpAddSmulStatement
import Theorems.Thm_GlobalTheory_HCA_exists_apOp_add_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory
open scoped ContDiff BoundedContinuousFunction
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (d m m' : ℕ) (U : Set (E d)) (a a' : (n : ℕ) → (Fin n → Fin d) → E d → ℂ) (t : ℂ), m' ≤ m → (∀ n w, ContDiffOn ℝ ∞ (a n w) U) → (∀ n w, ContDiffOn ℝ ∞ (a' n w) U) → ∃ a'' : (n : ℕ) → (Fin n → Fin d) → E d → ℂ, (∀ n w, ContDiffOn ℝ ∞ (a'' n w) U) ∧ (∀ x ξ : E d, symb m a'' x ξ = symb m a x ξ + if m' = m then t * symb m' a' x ξ else 0) ∧ ∀ (u : E d → ℂ) (x : E d), apOp m a'' u x = apOp m a u x + t * apOp m' a' u x := by
  first | exact @GlobalTheory.HCA.exists_apOp_add_smul | exact GlobalTheory.HCA.exists_apOp_add_smul | (intros; apply GlobalTheory.HCA.exists_apOp_add_smul <;> assumption)
end _root_.GlobalTheory.T
