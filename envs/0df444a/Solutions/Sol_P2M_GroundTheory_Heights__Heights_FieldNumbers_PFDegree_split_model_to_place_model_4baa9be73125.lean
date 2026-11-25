-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_PFDegree_split_model_to_place_model_4baa9be73125
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:11:46.456485+00:00
-- url     : https://prove2.me/submissions/7edd7924-4d17-451d-b472-56c97d07bd4a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PfContractedHypothesesExample
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_HomFracDegZeroEqFunField
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_AddBlockVarEquivFst
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsRename
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_ContractBlocksSplitPrime
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_splitVarEquiv_fst_fb4410ce5862
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_contractBlocks_splitPrime_59970ed6b43c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_pullDeg_split_8ca83a496a75
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_relDim_splitPrime_1aec8e01fe69
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_contract_funField_le_a56a7b1590a2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_AddBlockFunctionField_relDeg_inl_477d54fa0aab
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_relDim_eq_iff_hasRelDim_71dd155d571a


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
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.FieldNumbers
namespace PFDegree
theorem _root_.solution (h₁ : RenameMultiHomog.Statement.{u})
    (h₂ : RenameIntNum.Statement.{u}) (h₃ : RenameMultiProjPrime.Statement.{u})
    (h₄ : SplitRelDeg.Statement.{u}) (hB : IndefiniteRowSideFullHecke.FieldNumbers.PFDegree.Statement.{u, 0, 0, 0}) :
    ProjectionFormulaDegree.Statement.{u} := by
  classical
  intro F _ K K' _ _ _ _ j ι' _ P' hP' n hP hc bs
  have := hP'.isPrime
  refine ⟨contract_funField_le h₁ j P', ?_⟩
  have hQ : IsMultiProjPrime (splitPrime j P') :=
    h₃ F _ K' _ ι' (splitBlockEquiv j) (splitVarEquiv j ι') (splitVarEquiv_fst j ι') P' hP'
  have h := hB F K (blockCompl j) (fun k => ι' (j k)) (fun l => ι' l.1) (splitPrime j P') hQ n
    (by
      rw [contractBlocks_splitPrime]
      exact (relDim_eq_iff_hasRelDim _ n).mp hc)
    (by
      refine (relDim_eq_iff_hasRelDim _ n).mp ?_
      rw [relDim_splitPrime]
      exact hP) bs
  rw [← AddBlockFunctionField.relDeg_inl, ← h₄, contractBlocks_splitPrime] at h
  rw [← h]
  have h2 := h₂ F _ K' _ ι' (splitBlockEquiv j) (splitVarEquiv j ι') (splitVarEquiv_fst j ι') P' n
    (fun i => IndefiniteRowSideFullHecke.FieldNumbers.pullDeg (L := blockCompl j) (bs i))
  simp only [pullDeg_split] at h2
  exact h2.symm
end PFDegree
end GroundTheory.Heights₂.Heights.FieldNumbers
