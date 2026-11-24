-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_ProjectionFormulaContracted_hypotheses_example_9fbe5bc3ae39
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:43:28.722431+00:00
-- url     : https://prove2.me/submissions/0c174cb1-77db-4ff4-9b13-74abb5b2088c

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
namespace ProjectionFormulaContracted
theorem _root_.solution :
    IsMultiProjPrime (⊥ : Ideal (MRing (addBlock (ProjIdx 0) 1) ℚ)) ∧
      relDim (⊥ : Ideal (MRing (addBlock (ProjIdx 0) 1) ℚ)) = (1 : ℕ) ∧
      relDim (contractPrime Function.Embedding.some
        (⊥ : Ideal (MRing (addBlock (ProjIdx 0) 1) ℚ))) < (1 : ℕ) := by
  refine ⟨isMultiProjPrime_bot, ?_, ?_⟩
  · rw [relDim_bot]
    rfl
  · rw [contractPrime_bot, relDim_bot]
    show (((0 : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ)) < (((1 : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ))
    exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr (by norm_num))
end ProjectionFormulaContracted
end GroundTheory.Heights₂.Heights.FieldNumbers
