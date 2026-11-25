-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_contractBlocks_splitPrime_59970ed6b43c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:53:23.637421+00:00
-- url     : https://prove2.me/submissions/ccac5f0f-75b1-4a7b-b98e-9e632049bb7c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PfContractedHypothesesExample
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_HomFracDegZeroEqFunField
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_AddBlockVarEquivFst
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsRename
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_ContractBlocksSplitPrime

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
variable {K K' : Type} (j : K ↪ K') (ι' : K' → Type)
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution {F : Type u} [Field F] (P' : Ideal (MRing ι' F)) :
    IndefiniteRowSideFullHecke.FieldNumbers.contractBlocks (fun l : blockCompl j => ι' l.1) (splitPrime j P') =
      contractPrime j P' := by
  ext p
  unfold IndefiniteRowSideFullHecke.FieldNumbers.contractBlocks splitPrime contractPrime IndefiniteRowSideFullHecke.FieldNumbers.blockIncl
  simp only [Ideal.mem_comap]
  have e : rename (splitVar j ι') (rename (fun x : Σ k, ι' (j k) =>
      (⟨Sum.inl x.1, x.2⟩ : Σ s, splitCoord j ι' s)) p) = rename (blockIncl j ι') p := by
    rw [rename_rename]
    rfl
  exact iff_of_eq (congrArg (· ∈ P') e)
end GroundTheory.Heights₂.Heights.FieldNumbers
