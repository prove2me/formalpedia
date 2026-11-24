-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRational_hypotheses_example_4051c0ae0704
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:08:45.048854+00:00
-- url     : https://prove2.me/submissions/26adf6d9-9c66-4d8a-b94d-a840b17bfbdd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsExamples
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_relDim_projectiveSpace_e590f169e76b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_coordinate_isMultiHomog_e8b5927ae14d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_coordinate_not_mem_bot_75c44ca82dc1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_isMultiProjPrime_bot_dfd17cf75014


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
namespace CutRational
theorem _root_.solution :
    IsMultiProjPrime (⊥ : Ideal (MRing (ProjIdx 1) ℚ)) ∧
      relDim (⊥ : Ideal (MRing (ProjIdx 1) ℚ)) = 1 ∧
      IsMultiHomog (X ⟨(), 0⟩ : MRing (ProjIdx 1) ℚ) (blockWeight (ProjIdx 1) ⟨(), 0⟩) ∧
      IsMultiHomog (X ⟨(), 1⟩ : MRing (ProjIdx 1) ℚ) (blockWeight (ProjIdx 1) ⟨(), 0⟩) ∧
      (X ⟨(), 0⟩ : MRing (ProjIdx 1) ℚ) ∉ (⊥ : Ideal (MRing (ProjIdx 1) ℚ)) ∧
      (X ⟨(), 1⟩ : MRing (ProjIdx 1) ℚ) ∉ (⊥ : Ideal (MRing (ProjIdx 1) ℚ)) := by
  refine ⟨isMultiProjPrime_bot, ?_, coordinate_isMultiHomog 1 0, coordinate_isMultiHomog 1 1,
    coordinate_not_mem_bot 1 0, coordinate_not_mem_bot 1 1⟩
  rw [relDim_projectiveSpace]
  rfl
end CutRational
end GroundTheory.Heights₂.Heights.FieldNumbers
