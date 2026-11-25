-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_HookSum_card_hookShape_20885ef91065
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:52:55.582826+00:00
-- url     : https://prove2.me/submissions/865df7a9-7377-49fe-a7dd-f1f30fc19551

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PowerSums
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Expand
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PHookCharacterSumIdentity
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_HookSum_card_filter_one_le_le_8f085ebe469f

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
open GroundTheory.Heights₂.Heights.RestTerms.HookSum
namespace GroundTheory.Heights₂.Heights.RestTerms.HookSum
theorem _root_.solution (r k l : ℕ) (hl : l < r) :
    (Finset.univ.filter fun i : Fin r => (i : ℕ) ≠ 0 ∧ hookShape r k l i = 1).card = l := by
  have h : (Finset.univ.filter fun i : Fin r => (i : ℕ) ≠ 0 ∧ hookShape r k l i = 1) =
      (Finset.univ.filter fun j : Fin r => 1 ≤ (j : ℕ) ∧ (j : ℕ) ≤ l) := by
    apply Finset.filter_congr
    intro i _
    simp only [hookShape]
    by_cases h0 : (i : ℕ) = 0
    · rw [if_pos h0]; omega
    · by_cases h1 : (i : ℕ) ≤ l
      · rw [if_neg h0, if_pos h1]; omega
      · rw [if_neg h0, if_neg h1]; omega
  rw [h, card_filter_one_le_le r l hl]
end GroundTheory.Heights₂.Heights.RestTerms.HookSum
