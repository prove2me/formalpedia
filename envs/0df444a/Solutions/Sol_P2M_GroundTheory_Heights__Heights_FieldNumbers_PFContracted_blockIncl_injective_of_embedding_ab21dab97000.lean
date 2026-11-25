-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_blockIncl_injective_of_embedding_ab21dab97000
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:11:11.266515+00:00
-- url     : https://prove2.me/submissions/988f854a-19ae-4e6f-8fd1-13a1667ea3e7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_ContractBlocksSplitPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PRenameHilbFn
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PRenameIntNum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PRelevantPrimeDimGe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_ContractRelevant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_BlockInclInjectiveOfEmbedding

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
namespace PFContracted
theorem _root_.solution {K K' : Type} (j : K ↪ K') (ι' : K' → Type) :
    Function.Injective (blockIncl j ι') := by
  rintro ⟨k₁, x₁⟩ ⟨k₂, x₂⟩ h
  obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.mp h
  cases j.injective h1
  cases eq_of_heq h2
  rfl
end PFContracted
end GroundTheory.Heights₂.Heights.FieldNumbers
