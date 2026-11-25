-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_ContractRelDimLe_proof_46b509c2b5c3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:28:47.647493+00:00
-- url     : https://prove2.me/submissions/39378c33-0f20-4de3-9e0b-130270a13d10

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsContractRelDimLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContracted
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PContractRelDimLe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_ContractRelDimLe_ringKrullDim_killIdeal_add_card_le_2f11af28706c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_ContractRelDimLe_ringKrullDim_contract_eq_killIdeal_facff24de20d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_contractPrime_isRelevant_e828c0104b5a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_contractPrime_killStable_2361f4b4da88
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_exists_ringKrullDim_eq_65838c645fa5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_killBlocks_mem_of_isMultiHomogIdeal_8504d8e804fa
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_relDim_eq_int_8d437d865d06


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
namespace GroundTheory.Heights₂.Heights.FieldNumbers.ContractRelDimLe
theorem _root_.solution : ContractRelDimLe.Statement.{u} := by
  intro F _ K K' _ _ _ _ j ι' _ P' hP'
  have := hP'.isPrime
  have hstab : ∀ (T : Finset K') (q : MRing ι' F), q ∈ P' → killBlocks T q ∈ P' :=
    fun T _ hq => killBlocks_mem_of_isMultiHomogIdeal hP'.multiHomog T hq
  obtain ⟨D', -, hD'⟩ := exists_ringKrullDim_eq hstab hP'.relevant
  obtain ⟨D, -, hD⟩ := exists_ringKrullDim_eq (Q := contractPrime j P')
    (contractPrime_killStable j ι' hP'.multiHomog) (contractPrime_isRelevant j ι' hP'.relevant)
  have hchain := ringKrullDim_killIdeal_add_card_le hstab hP'.relevant (Finset.univ.map j)ᶜ
  rw [← ringKrullDim_contract_eq_killIdeal, hD, hD', ← Nat.cast_add] at hchain
  have hle : D + ((Finset.univ.map j)ᶜ).card ≤ D' := by exact_mod_cast hchain
  have hcard : ((Finset.univ.map j)ᶜ).card + Fintype.card K = Fintype.card K' := by
    rw [Finset.card_compl, Finset.card_map, Finset.card_univ]
    have := Fintype.card_le_of_embedding j
    omega
  rw [relDim_eq_int hD, relDim_eq_int hD']
  exact WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr (by omega))
end GroundTheory.Heights₂.Heights.FieldNumbers.ContractRelDimLe
