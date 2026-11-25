-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_mem_contractPrime_inl_iff_20c191697d9f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:24:34.421378+00:00
-- url     : https://prove2.me/submissions/9d24d1b0-ef47-4132-af60-a5fd3b8718c6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsRename
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_ContractBlocksSplitPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PRenameMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PSplitRelDeg
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_rename_splitVar_blockIncl_inl_10b826c66fda

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
variable {F : Type u} [Field F] {K K' : Type} (j : K ↪ K') {ι' : K' → Type}
  (P' : Ideal (MRing ι' F)) [P'.IsPrime]
omit [P'.IsPrime]
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution (g : MRing (fun k => ι' (j k)) F) :
    g ∈ contractPrime (Function.Embedding.inl : K ↪ K ⊕ blockCompl j) (splitPrime j P') ↔
      g ∈ contractPrime j P' :=
  iff_of_eq (congrArg (· ∈ P') (rename_splitVar_blockIncl_inl j g))
end GroundTheory.Heights₂.Heights.FieldNumbers
