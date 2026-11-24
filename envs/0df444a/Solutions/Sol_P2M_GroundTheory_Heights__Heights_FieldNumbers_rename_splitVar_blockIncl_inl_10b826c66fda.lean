-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_rename_splitVar_blockIncl_inl_10b826c66fda
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:07:50.955592+00:00
-- url     : https://prove2.me/submissions/d6433763-e5f6-4707-8615-7c0e39acae7b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsRename
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_ContractBlocksSplitPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PRenameMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PSplitRelDeg

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
theorem _root_.solution {R : Type*} [CommSemiring R]
    (f : MvPolynomial (Σ k, ι' (j k)) R) :
    rename (splitVar j ι')
        (rename (blockIncl (Function.Embedding.inl : K ↪ K ⊕ blockCompl j) (splitCoord j ι')) f) =
      rename (blockIncl j ι') f :=
  (rename_rename _ _ f).trans rfl
end GroundTheory.Heights₂.Heights.FieldNumbers
