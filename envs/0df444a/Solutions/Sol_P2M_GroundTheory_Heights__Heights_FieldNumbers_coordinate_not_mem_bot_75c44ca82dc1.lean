-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_coordinate_not_mem_bot_75c44ca82dc1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:02:23.270123+00:00
-- url     : https://prove2.me/submissions/49addfbd-1e5b-42ac-b457-4156f6b2989a

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
    (X ⟨(), i⟩ : MRing (ProjIdx N) ℚ) ∉ (⊥ : Ideal (MRing (ProjIdx N) ℚ)) := by
  rw [Ideal.mem_bot]
  exact X_ne_zero _
end GroundTheory.Heights₂.Heights.FieldNumbers
