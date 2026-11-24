-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_coordinate_isMultiHomog_e8b5927ae14d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:32:48.609865+00:00
-- url     : https://prove2.me/submissions/48719bf0-9513-4d73-b91a-8a48f82ccfd4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsExamples

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
theorem _root_.solution (N : ℕ) (i : Fin (N + 1)) :
    IsMultiHomog (X ⟨(), i⟩ : MRing (ProjIdx N) ℚ) (blockWeight (ProjIdx N) ⟨(), 0⟩) :=
  isWeightedHomogeneous_X _ _ _
end GroundTheory.Heights₂.Heights.FieldNumbers
