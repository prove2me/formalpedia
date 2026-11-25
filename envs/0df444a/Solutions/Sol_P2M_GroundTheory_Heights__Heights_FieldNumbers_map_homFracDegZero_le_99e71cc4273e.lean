-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_map_homFracDegZero_le_99e71cc4273e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:21:28.81983+00:00
-- url     : https://prove2.me/submissions/a6034e00-0ecf-40c2-b0ff-a1977b955506

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDivPushForward
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PExistsForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PCutRational
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFDegree
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_isMultiHomog_rename_fd9a6cb3fd55
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_contractFracMap_algebraMap_39d4c423cc7f

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
variable [DecidableEq K] [DecidableEq K']
variable {F : Type u} [Field F]
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution (P' : Ideal (MRing ι' F)) [P'.IsPrime] :
    (homFracDegZero (contractPrime j P')).map (contractFracMap j P') ≤ homFracDegZero P' := by
  unfold homFracDegZero
  rw [IntermediateField.adjoin_map, IntermediateField.adjoin_le_iff]
  rintro _ ⟨x, ⟨b, f, g, hf, hg, hgP, rfl⟩, rfl⟩
  apply IntermediateField.subset_adjoin
  refine ⟨Function.extend j b 0, rename (blockIncl j ι') f, rename (blockIncl j ι') g,
    isMultiHomog_rename j ι' hf, isMultiHomog_rename j ι' hg, hgP, ?_⟩
  rw [map_div₀, contractFracMap_algebraMap, contractFracMap_algebraMap]
end GroundTheory.Heights₂.Heights.FieldNumbers
