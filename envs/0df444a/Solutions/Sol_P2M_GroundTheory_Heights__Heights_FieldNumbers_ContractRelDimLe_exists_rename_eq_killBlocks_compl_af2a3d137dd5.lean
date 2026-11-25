-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_ContractRelDimLe_exists_rename_eq_killBlocks_compl_af2a3d137dd5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:27:07.563258+00:00
-- url     : https://prove2.me/submissions/55d9cf65-77fd-49f1-aa5d-26b1cb15d67a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsContractRelDimLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContracted
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PContractRelDimLe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_killBlocks_X_a86018fe216d


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR PFContracted
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.FieldNumbers.ContractRelDimLe
variable {K K' : Type*} [Fintype K] [DecidableEq K] [Fintype K'] [DecidableEq K'] {F : Type*}
  [Field F] (j : K ↪ K') (ι' : K' → Type*)
omit [DecidableEq K]
namespace GroundTheory.Heights₂.Heights.FieldNumbers.ContractRelDimLe
theorem _root_.solution (x : MRing ι' F) :
    ∃ a : MRing (fun k => ι' (j k)) F,
      rename (blockIncl j ι') a = killBlocks (Finset.univ.map j)ᶜ x := by
  induction x using MvPolynomial.induction_on with
  | C c => exact ⟨C c, by simp [killBlocks]⟩
  | add p q hp hq =>
    obtain ⟨a, ha⟩ := hp
    obtain ⟨b, hb⟩ := hq
    exact ⟨a + b, by rw [map_add, ha, hb, map_add]⟩
  | mul_X p v hp =>
    obtain ⟨a, ha⟩ := hp
    obtain ⟨k', i⟩ := v
    rw [map_mul, killBlocks_X, ← ha]
    by_cases h : k' ∈ (Finset.univ.map j)ᶜ
    · exact ⟨0, by rw [if_pos h, mul_zero, map_zero]⟩
    · rw [if_neg h]
      simp only [Finset.mem_compl, Finset.mem_map, Finset.mem_univ, true_and, not_not] at h
      obtain ⟨k, rfl⟩ := h
      exact ⟨a * X ⟨k, i⟩, by rw [map_mul, rename_X]; rfl⟩
end GroundTheory.Heights₂.Heights.FieldNumbers.ContractRelDimLe
