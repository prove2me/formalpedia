-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_CharacterBound_proof_e3dff55e7f37
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:02:03.798234+00:00
-- url     : https://prove2.me/submissions/416f4667-e7aa-4ef2-9db5-d4120f2452d1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsComb
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCharacterBound
import Theorems.Thm_P2M_RH_P2M_GroundTheory_Heights__Heights_RestTerms_symmetricGroupCharacter_eq_cf_ddc4362c6d08_01d69069a647955c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_IsAlt_sum_a5fe0c99cdcf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_latticeWords_eq_empty_of_sum_ne_25cc7c9dcaf5


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
open MvPolynomial Finset Comb
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace CharacterBound
theorem _root_.solution (h1 : CombTableEqWords.Statement) (h2 : CombCfBound.Statement) :
    CharacterBound.Statement := by
  intro m lam rho hlam hrho
  rw [symmetricGroupCharacter_eq_cf]
  refine (h2 m rho hrho lam hlam).trans ?_
  by_cases hs : ∑ i, lam i = rho.sum
  · rw [h1 m lam hlam, hs]
  · rw [latticeWords_eq_empty_of_sum_ne _ _ hs, Finset.card_empty, Nat.cast_zero]
    exact Nat.cast_nonneg _
end CharacterBound
end GroundTheory.Heights₂.Heights.RestTerms
