-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_PFDegree_toIndefiniteRowSideFullHecke_a42574d499b7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:11:49.465056+00:00
-- url     : https://prove2.me/submissions/6811d261-ed68-4fe6-a354-bce54f78db03

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PfContractedHypothesesExample
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_HomFracDegZeroEqFunField
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_AddBlockVarEquivFst
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsRename
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_ContractBlocksSplitPrime
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_AddBlockFunctionField_pullDeg_inl_97aa8e9e178f
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
theorem _root_.solution (hA : ProjectionFormulaDegree.Statement.{u}) :
    IndefiniteRowSideFullHecke.FieldNumbers.PFDegree.Statement.{u, 0, 0, 0} := by
  intro F _ K _ _ L _ _ ι _ ι₂ _ P' hP' n hc hP bs
  have : ∀ s, Fintype (Sum.elim ι ι₂ s) := fun s => match s with
    | .inl k => (inferInstance : Fintype (ι k))
    | .inr l => (inferInstance : Fintype (ι₂ l))
  obtain ⟨-, h⟩ := hA F K (K ⊕ L) Function.Embedding.inl (Sum.elim ι ι₂) P' hP' n
    ((relDim_eq_iff_hasRelDim P' n).mpr hP)
    ((relDim_eq_iff_hasRelDim (IndefiniteRowSideFullHecke.FieldNumbers.contractBlocks ι₂ P') n).mpr hc) bs
  have := hP'.isPrime
  simp only [AddBlockFunctionField.pullDeg_inl, AddBlockFunctionField.relDeg_inl] at h
  exact h
end PFDegree
end GroundTheory.Heights₂.Heights.FieldNumbers
