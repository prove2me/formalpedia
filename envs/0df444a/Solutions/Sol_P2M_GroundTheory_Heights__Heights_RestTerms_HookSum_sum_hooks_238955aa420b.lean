-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_HookSum_sum_hooks_238955aa420b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:22:44.719099+00:00
-- url     : https://prove2.me/submissions/882d562f-8005-40f6-af04-6806f21020bb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PowerSums
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Expand
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PHookCharacterSumIdentity
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_HookSum_card_hookShape_20885ef91065
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_HookSum_hookShape_mem_3f5acd6499d7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_HookSum_hookShape_isHook_13714c2e5d51
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_HookSum_hook_classification_668125ac27af

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
theorem _root_.solution (r k : ℕ) (hk : 1 ≤ k) (g : (Fin r → ℕ) → ℚ) :
    ∑ nu ∈ partitionsOf r k, g nu *
        (if ∀ i : Fin r, (i : ℕ) ≠ 0 → nu i ≤ 1 then
          (-1 : ℚ) ^ ((Finset.univ.filter fun i : Fin r => (i : ℕ) ≠ 0 ∧ nu i = 1).card)
        else 0) =
      ∑ l ∈ Finset.range (min r k), (-1 : ℚ) ^ l * g (hookShape r k l) := by
  simp only [mul_ite, mul_zero]
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_nbij' (fun l => hookShape r k l)
    (fun nu => (Finset.univ.filter fun i : Fin r => (i : ℕ) ≠ 0 ∧ nu i = 1).card)
  · intro l hl
    rw [Finset.mem_range, lt_min_iff] at hl
    rw [Finset.mem_filter]
    exact ⟨hookShape_mem r k l hl.1 hl.2, hookShape_isHook r k l⟩
  · intro nu hnu
    rw [Finset.mem_filter] at hnu
    obtain ⟨h1, h2, -⟩ := hook_classification hk hnu.1 hnu.2 rfl
    rw [Finset.mem_range, lt_min_iff]
    exact ⟨h1, h2⟩
  · intro l hl
    rw [Finset.mem_range, lt_min_iff] at hl
    exact card_hookShape r k l hl.1
  · intro nu hnu
    rw [Finset.mem_filter] at hnu
    exact (hook_classification hk hnu.1 hnu.2 rfl).2.2
  · intro l hl
    rw [Finset.mem_range, lt_min_iff] at hl
    rw [card_hookShape r k l hl.1, mul_comm]
end GroundTheory.Heights₂.Heights.RestTerms.HookSum
