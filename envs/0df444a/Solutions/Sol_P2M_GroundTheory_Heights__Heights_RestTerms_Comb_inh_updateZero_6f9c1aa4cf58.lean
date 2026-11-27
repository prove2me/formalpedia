-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Comb_inh_updateZero_6f9c1aa4cf58
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:08:33.340416+00:00
-- url     : https://prove2.me/submissions/68b55eac-1eb5-48de-b248-ff67a8d55c82

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsComb
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_InhabitantsComb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_isAlt_vandermonde_mul_prod_b74d8ff779cf


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset Equiv Comb
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace Comb
theorem _root_.solution :
    IsAlt (alternantPsum 2 [1]) ∧ Antitone (![1, 1] : Fin 2 → ℕ) ∧
      1 ≤ (![1, 1] : Fin 2 → ℕ) 0 + stair 2 0 ∧
      ¬ Antitone (Function.update (![1, 1] : Fin 2 → ℕ) 0 ((![1, 1] : Fin 2 → ℕ) 0 - 1)) := by
  refine ⟨isAlt_vandermonde_mul_prod _, ?_, by decide, ?_⟩
  · intro i j h; fin_cases i <;> fin_cases j <;> simp_all
  · intro h
    have := h (show (0 : Fin 2) ≤ 1 by decide)
    simp at this
end Comb
end GroundTheory.Heights₂.Heights.RestTerms
