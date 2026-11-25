-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_ContractRelDimLe_ringKrullDim_killIdeal_add_card_le_2f11af28706c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:27:09.828091+00:00
-- url     : https://prove2.me/submissions/fb5b887f-7957-45e8-bb17-b2e3b917537f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsContractRelDimLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContracted
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PContractRelDimLe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_killBlocks_X_a86018fe216d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_killBlocks_comp_f21ab6d300e7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_killBlocks_empty_1d848d6dfd22
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_ringKrullDim_add_one_le_36765965af2f


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
variable {K : Type*} [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]
namespace GroundTheory.Heights₂.Heights.FieldNumbers.ContractRelDimLe
theorem _root_.solution {Q : Ideal (MRing ι F)} [Q.IsPrime]
    (hQ : ∀ (T : Finset K) (q : MRing ι F), q ∈ Q → killBlocks T q ∈ Q) (hrel : IsRelevant Q)
    (T : Finset K) :
    ringKrullDim (MRing ι F ⧸ killIdeal Q T) + (T.card : WithBot ℕ∞) ≤
      ringKrullDim (MRing ι F ⧸ Q) := by
  choose i hi using hrel
  have hmono : ∀ {T T' : Finset K}, T ⊆ T' → killIdeal Q T ≤ killIdeal Q T' := by
    intro T T' h q hq
    change killBlocks T' q ∈ Q
    rw [← killBlocks_comp h]
    exact hQ T' _ hq
  induction T using Finset.induction_on with
  | empty =>
    have : killIdeal Q (∅ : Finset K) = Q := by
      ext q
      simp [killIdeal, killBlocks_empty]
    rw [this, Finset.card_empty, Nat.cast_zero, add_zero]
  | insert k T hk ih =>
    have : (killIdeal Q T).IsPrime := Ideal.comap_isPrime _ _
    have hstep := ringKrullDim_add_one_le (P := killIdeal Q T) (Q := killIdeal Q (insert k T))
      (hmono (Finset.subset_insert k T)) (f := X ⟨k, i k⟩)
      (by
        change killBlocks T (X ⟨k, i k⟩) ∉ Q
        rw [killBlocks_X, if_neg hk]
        exact hi k)
      (by
        change killBlocks (insert k T) (X ⟨k, i k⟩) ∈ Q
        rw [killBlocks_X, if_pos (Finset.mem_insert_self k T)]
        exact Q.zero_mem)
    calc ringKrullDim (MRing ι F ⧸ killIdeal Q (insert k T)) + ((insert k T).card : WithBot ℕ∞)
        = (ringKrullDim (MRing ι F ⧸ killIdeal Q (insert k T)) + 1) + (T.card : WithBot ℕ∞) := by
          rw [Finset.card_insert_of_notMem hk, Nat.cast_add, Nat.cast_one, add_assoc,
            add_comm (1 : WithBot ℕ∞)]
      _ ≤ ringKrullDim (MRing ι F ⧸ killIdeal Q T) + (T.card : WithBot ℕ∞) := by gcongr
      _ ≤ _ := ih
end GroundTheory.Heights₂.Heights.FieldNumbers.ContractRelDimLe
