-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_SplitRelDeg_proof_9b289c5f4e63
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:23:02.59116+00:00
-- url     : https://prove2.me/submissions/86460d8a-c02b-41e0-9772-b72e14127ec3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsRename
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_ContractBlocksSplitPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PRenameMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PSplitRelDeg
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_map_splitFracMap_homFracDegZero_de5b75c72070
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_map_splitFracMap_contract_f14e9153186b

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
namespace SplitRelDeg
theorem _root_.solution : SplitRelDeg.Statement.{u} := by
  intro F _ K K' _ _ j ι' P' _
  unfold relDeg
  have h := IntermediateField.relfinrank_map_map
    ((homFracDegZero (contractPrime (Function.Embedding.inl : K ↪ K ⊕ blockCompl j)
        (splitPrime j P'))).map (contractFracMap Function.Embedding.inl (splitPrime j P')))
    (homFracDegZero (splitPrime j P')) (splitFracMap j P')
  rw [map_splitFracMap_contract, map_splitFracMap_homFracDegZero] at h
  exact h
end SplitRelDeg
end GroundTheory.Heights₂.Heights.FieldNumbers
