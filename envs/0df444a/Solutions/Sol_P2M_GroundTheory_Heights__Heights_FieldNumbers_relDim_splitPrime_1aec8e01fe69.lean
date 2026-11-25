-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_relDim_splitPrime_1aec8e01fe69
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:54:02.970963+00:00
-- url     : https://prove2.me/submissions/3df29d6c-ba46-4461-a785-bd9ddbeeb3c9

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
theorem _root_.solution {F : Type u} [Field F] [Fintype K] [Fintype K'] [Fintype (blockCompl j)]
    (P' : Ideal (MRing ι' F)) : relDim (splitPrime j P') = relDim P' := by
  have e : MRing (splitCoord j ι') F ⧸ splitPrime j P' ≃+* MRing ι' F ⧸ P' :=
    Ideal.quotientEquiv _ _ (renameEquiv F (splitVarEquiv j ι')).toRingEquiv
      (Ideal.map_comap_of_surjective _ (renameEquiv F (splitVarEquiv j ι')).surjective P').symm
  unfold relDim
  rw [ringKrullDim_eq_of_ringEquiv e, Fintype.card_congr (splitBlockEquiv j)]
end GroundTheory.Heights₂.Heights.FieldNumbers
