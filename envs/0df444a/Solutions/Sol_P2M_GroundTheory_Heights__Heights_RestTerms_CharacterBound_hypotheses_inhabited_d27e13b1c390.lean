-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_CharacterBound_hypotheses_inhabited_d27e13b1c390
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:32:25.095695+00:00
-- url     : https://prove2.me/submissions/0d0201d6-2128-4ed0-ae6e-4082d5007b5d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements

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
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace CharacterBound
theorem _root_.solution :
    Antitone (![2, 1] : Fin 2 → ℕ) ∧ ∀ q ∈ [2, 1], 1 ≤ q := by
  refine ⟨?_, by simp⟩
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all
end CharacterBound
end GroundTheory.Heights₂.Heights.RestTerms
