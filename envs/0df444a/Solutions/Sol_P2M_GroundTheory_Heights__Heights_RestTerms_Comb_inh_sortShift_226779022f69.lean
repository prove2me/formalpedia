-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Comb_inh_sortShift_226779022f69
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:08:25.316888+00:00
-- url     : https://prove2.me/submissions/13ab486c-88e2-4fee-8ca9-63a3e5416908

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsComb
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_InhabitantsComb

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
    Antitone (![2, 1] : Fin 2 → ℕ) ∧ 1 ≤ (![2, 1] : Fin 2 → ℕ) 0 + stair 2 0 ∧
      Function.Injective (Function.update (fun j => (![2, 1] : Fin 2 → ℕ) j + stair 2 j) 0
        ((![2, 1] : Fin 2 → ℕ) 0 + stair 2 0 - 1)) := by
  refine ⟨?_, by decide, ?_⟩
  · intro i j h; fin_cases i <;> fin_cases j <;> simp_all
  · intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [stair, Function.update]
end Comb
end GroundTheory.Heights₂.Heights.RestTerms
