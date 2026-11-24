-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_relDim_projectiveSpace_e590f169e76b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:41:40.692031+00:00
-- url     : https://prove2.me/submissions/2c0c597a-c03d-4697-899a-87841391c973

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsExamples
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_relDim_bot_6b440164bc02

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
theorem _root_.solution {F : Type*} [Field F] (N : ℕ) :
    relDim (⊥ : Ideal (MRing (ProjIdx N) F)) = (N : WithBot (WithTop ℤ)) := by
  rw [relDim_bot]
  simp [Fintype.card_sigma]
  rfl
end GroundTheory.Heights₂.Heights.FieldNumbers
