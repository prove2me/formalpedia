-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_killBlocks_comp_f21ab6d300e7
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:21:26.681359+00:00
-- url     : https://prove2.me/submissions/46a4aaf3-65ff-49e3-a4f5-836dcc537ac4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContractedDim
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_killBlocks_X_a86018fe216d

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
open GroundTheory.Heights₂.Heights.FieldNumbers.PFContracted
variable {K : Type*} [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]
namespace GroundTheory.Heights₂.Heights.FieldNumbers.PFContracted
theorem _root_.solution {T T' : Finset K} (h : T ⊆ T') :
    (killBlocks (ι := ι) (F := F) T').comp (killBlocks T) = killBlocks T' := by
  apply MvPolynomial.algHom_ext
  intro v
  simp only [AlgHom.comp_apply, killBlocks_X]
  by_cases hv : v.1 ∈ T
  · simp [hv, h hv]
  · simp [hv, killBlocks_X]
end GroundTheory.Heights₂.Heights.FieldNumbers.PFContracted
