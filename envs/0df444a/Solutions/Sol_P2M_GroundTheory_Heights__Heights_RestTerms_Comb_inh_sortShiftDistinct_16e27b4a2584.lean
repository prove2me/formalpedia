-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Comb_inh_sortShiftDistinct_16e27b4a2584
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:08:19.891833+00:00
-- url     : https://prove2.me/submissions/b0fd4635-edad-43bc-b2c3-f45405c00a36

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
    Function.Injective (![3, 1] : Fin 2 → ℕ) ∧ 1 ≤ 1 ∧ (0 : Fin 2) ≠ 1 ∧
      1 ≤ (![3, 1] : Fin 2 → ℕ) 0 ∧ 1 ≤ (![3, 1] : Fin 2 → ℕ) 1 := by
  refine ⟨?_, le_rfl, by decide, by decide, by decide⟩
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all
end Comb
end GroundTheory.Heights₂.Heights.RestTerms
