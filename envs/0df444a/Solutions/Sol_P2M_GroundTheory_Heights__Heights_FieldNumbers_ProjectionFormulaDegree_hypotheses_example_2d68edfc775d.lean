-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_ProjectionFormulaDegree_hypotheses_example_2d68edfc775d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:43:28.608798+00:00
-- url     : https://prove2.me/submissions/79a76587-0a69-4fb6-a49e-ede277934650

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsExamples
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_relDim_bot_6b440164bc02
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_contractPrime_bot_230ea120a67d
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
namespace ProjectionFormulaDegree
theorem _root_.solution :
    IsMultiProjPrime (⊥ : Ideal (MRing (addBlock (ProjIdx 1) 0) ℚ)) ∧
      relDim (⊥ : Ideal (MRing (addBlock (ProjIdx 1) 0) ℚ)) = (1 : ℕ) ∧
      relDim (contractPrime Function.Embedding.some
        (⊥ : Ideal (MRing (addBlock (ProjIdx 1) 0) ℚ))) = (1 : ℕ) := by
  refine ⟨isMultiProjPrime_bot, ?_, ?_⟩
  · rw [relDim_bot]
    rfl
  · rw [contractPrime_bot, relDim_bot]
    rfl
end ProjectionFormulaDegree
end GroundTheory.Heights₂.Heights.FieldNumbers
