-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_splitFracMap_contractFracMap_inl_mk_c258701bd505
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:24:43.640035+00:00
-- url     : https://prove2.me/submissions/070b8d6f-6af7-4a01-b55f-f12b54ba9543

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsRename
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_ContractBlocksSplitPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PRenameMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PSplitRelDeg
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_splitFracMap_mk_90d3ee9fcc29
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_contractFracMap_mk_c349b29b8888
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
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution (f : MRing (fun k => ι' (j k)) F) :
    splitFracMap j P' (contractFracMap (Function.Embedding.inl : K ↪ K ⊕ blockCompl j)
        (splitPrime j P') (algebraMap _ _
          (Ideal.Quotient.mk (contractPrime Function.Embedding.inl (splitPrime j P')) f))) =
      contractFracMap j P' (algebraMap _ _ (Ideal.Quotient.mk (contractPrime j P') f)) := by
  have h1 := contractFracMap_mk (Function.Embedding.inl : K ↪ K ⊕ blockCompl j) (splitPrime j P') f
  have h2 := splitFracMap_mk j P' (rename (blockIncl Function.Embedding.inl (splitCoord j ι')) f)
  have h3 := contractFracMap_mk j P' f
  have h4 := rename_splitVar_blockIncl_inl j (R := F) f
  exact (congrArg (splitFracMap j P') h1).trans (h2.trans ((congrArg (fun p =>
    algebraMap (MRing ι' F ⧸ P') (FractionRing (MRing ι' F ⧸ P')) (Ideal.Quotient.mk P' p)) h4).trans
      h3.symm))
end GroundTheory.Heights₂.Heights.FieldNumbers
