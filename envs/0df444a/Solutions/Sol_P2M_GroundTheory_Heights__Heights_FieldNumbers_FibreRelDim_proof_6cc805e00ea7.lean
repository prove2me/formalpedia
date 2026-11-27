-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_FibreRelDim_proof_6cc805e00ea7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:55:54.140753+00:00
-- url     : https://prove2.me/submissions/06652453-6185-4a89-a0bf-659a91bca50f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsFibreRelDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PContractRelDimLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PFibreRelDim
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_ContractRelDimLe_proof_46b509c2b5c3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRational_proof_c27e72dcc134
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_ExistsForm_proof_d5dace6f400d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_exists_ringKrullDim_eq_65838c645fa5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_killBlocks_mem_of_isMultiHomogIdeal_8504d8e804fa
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_natCast_withBot_withTop_eb5b1b957aeb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_proof_c7e248874611
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_relDim_eq_int_8d437d865d06
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_ringKrullDim_add_one_le_36765965af2f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_ProjectionFormulaDegree_proof_0aacacc92e0d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_RelevantPrimeDimGe_proof_f3a1f51a2659


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
namespace GroundTheory.Heights₂.Heights.FieldNumbers
namespace FibreRelDim
theorem _root_.solution : FibreRelDim.Statement.{u} := by
  intro F _ K K' _ _ _ _ j ι' _ P' hP' n hP'n hPn W _ hWn _ W' hW'
  obtain ⟨hW'm, hPW', hcW'⟩ := hW'
  have := hP'.isPrime
  have := hW'm.isPrime

  have hge : ((n : ℕ) : WithBot (WithTop ℤ)) ≤ relDim W' := by
    rw [← hWn, ← hcW']
    exact ContractRelDimLe.proof F K K' j ι' W' hW'm

  have hne : ¬ W' ≤ P' := by
    intro hle
    have heq : W' = P' := le_antisymm hle hPW'
    rw [heq] at hcW'
    rw [hcW', hWn] at hPn
    have := congrArg (fun x : WithBot (WithTop ℤ) => x) hPn
    rw [natCast_withBot_withTop, natCast_withBot_withTop] at this
    have h2 := WithTop.coe_injective (WithBot.coe_injective this)
    omega
  obtain ⟨f, hfW', hfP'⟩ := Set.not_subset.mp hne
  have hstab : ∀ {Q : Ideal (MRing ι' F)}, IsMultiProjPrime Q →
      ∀ (T : Finset K') (q : MRing ι' F), q ∈ Q → killBlocks T q ∈ Q :=
    fun hQ T _ hq => killBlocks_mem_of_isMultiHomogIdeal hQ.multiHomog T hq
  obtain ⟨D', -, hD'⟩ := exists_ringKrullDim_eq (hstab hP') hP'.relevant
  obtain ⟨D, -, hD⟩ := exists_ringKrullDim_eq (hstab hW'm) hW'm.relevant
  have hstep := ringKrullDim_add_one_le hPW' hfP' hfW'
  rw [hD, hD'] at hstep
  have hlt : D + 1 ≤ D' := by exact_mod_cast hstep
  rw [relDim_eq_int hD', natCast_withBot_withTop] at hP'n
  have hP'z := WithTop.coe_injective (WithBot.coe_injective hP'n)
  rw [relDim_eq_int hD, natCast_withBot_withTop] at hge ⊢
  have hgez : (n : ℤ) ≤ (D : ℤ) - Fintype.card K' :=
    WithTop.coe_le_coe.mp (WithBot.coe_le_coe.mp hge)
  congr 2
  push_cast at hP'z
  omega
end FibreRelDim
end GroundTheory.Heights₂.Heights.FieldNumbers
