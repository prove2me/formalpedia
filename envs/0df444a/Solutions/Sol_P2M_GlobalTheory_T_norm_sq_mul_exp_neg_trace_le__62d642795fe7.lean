-- Prove2me | solution 1 for P2M_GlobalTheory_T_norm_sq_mul_exp_neg_trace_le__62d642795fe7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:34:37.206245+00:00
-- url     : https://prove2.me/submissions/2fbd57a6-9c29-42f6-a158-263eebbd419d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormSqMulExpNegTraceLe
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormSqMulExpNegTraceLeStatement
import Theorems.Thm_GlobalTheory_norm_sq_mul_exp_neg_trace_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (δ : ℝ), 0 < δ → ∃ C : ℝ, ∀ x : F, (∀ τ : Emb F, 0 < τ x) → |(Algebra.norm ℚ x : ℝ)| ^ 2 * Real.exp (-δ * ∑ τ : Emb F, τ x) ≤ C * Real.exp (-(δ / 2) * ∑ τ : Emb F, τ x) := by
  first | exact @GlobalTheory.norm_sq_mul_exp_neg_trace_le | exact GlobalTheory.norm_sq_mul_exp_neg_trace_le | (intros; apply GlobalTheory.norm_sq_mul_exp_neg_trace_le <;> assumption)
end _root_.GlobalTheory.T
