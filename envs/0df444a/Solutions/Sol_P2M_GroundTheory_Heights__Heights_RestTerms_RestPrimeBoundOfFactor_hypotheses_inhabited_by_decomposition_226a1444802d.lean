-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_RestPrimeBoundOfFactor_hypotheses_inhabited_by_decomposition_226a1444802d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:08:29.615542+00:00
-- url     : https://prove2.me/submissions/9b46f3a8-937f-42fa-9f39-550f0fae4b5e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsElem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Inhabitants
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Elementary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_InhabitantsElem
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_inh_restTerm_b831e71f17f7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_inh_J_eq_083d9017b1ba
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_inh_decomp_c8d39b1d7eb7


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace RestPrimeBoundOfFactor
theorem _root_.solution :
    IsPowerSumDecomposition 1 (1 + 1) (restPolynomial 1 1 1 .last) inhQ ∧
    restTerm 1 (1 + 1) inhQ 2 0 (smallPowerSum 1 1 1 .last (2 - 1) 0) ≠ 0 ∧
    ∀ k : ℕ, 2 ≤ k → k ≤ 1 + 1 → ∀ τ τ' : Fin 1,
        |restTerm 1 (1 + 1) inhQ k τ (smallPowerSum 1 1 1 .last (k - 1) τ')| ≤
          ((1 * (1 * 1) + 1 : ℕ) : ℚ) * |fibreDegree 1 1 1 .last| * restX 1 1 ^ (k - 1) /
            (k.factorial : ℚ) := by
  refine ⟨inh_decomp, by rw [inh_restTerm]; norm_num, ?_⟩
  intro k hk2 hk τ τ'
  obtain rfl : k = 2 := by omega
  rw [inh_restTerm, inh_J_eq]
  norm_num [restX, Nat.factorial_two]
end RestPrimeBoundOfFactor
end GroundTheory.Heights₂.Heights.RestTerms
