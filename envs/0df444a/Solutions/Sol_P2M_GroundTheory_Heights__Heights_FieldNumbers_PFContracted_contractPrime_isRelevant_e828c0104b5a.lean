-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_contractPrime_isRelevant_e828c0104b5a
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:23:23.161121+00:00
-- url     : https://prove2.me/submissions/1cc18064-c717-4ad0-9b12-d0bd069d7877

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContractedDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContracted

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
open GroundTheory.Heights₂.Heights.FieldNumbers.PFContracted
variable {K K' : Type*} [DecidableEq K] [DecidableEq K'] {F : Type*} [Field F]
namespace GroundTheory.Heights₂.Heights.FieldNumbers.PFContracted
theorem _root_.solution (j : K ↪ K') (ι' : K' → Type*) {P' : Ideal (MRing ι' F)}
    (h : IsRelevant P') : IsRelevant (contractPrime j P') := by
  intro k
  obtain ⟨i, hi⟩ := h (j k)
  refine ⟨i, ?_⟩
  change rename (blockIncl j ι') (X ⟨k, i⟩) ∉ P'
  rw [rename_X]
  exact hi
end GroundTheory.Heights₂.Heights.FieldNumbers.PFContracted
