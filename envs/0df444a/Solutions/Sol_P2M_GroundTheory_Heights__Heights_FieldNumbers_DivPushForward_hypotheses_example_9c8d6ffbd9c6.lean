-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_DivPushForward_hypotheses_example_9c8d6ffbd9c6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:08:10.111767+00:00
-- url     : https://prove2.me/submissions/43209a35-b269-48f1-ba56-8969d911173e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsExamples
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDivPushForward
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRational_hypotheses_example_4051c0ae0704
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_hypotheses_example_aa81192740bc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbDegreeBound_hypotheses_example_0ca615a70965
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbExactDivide_hypotheses_example_499b36c3f9ca
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_IntNumBaseChange_hypotheses_example_41a071ddf012
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_IntNumBase_hypotheses_example_77f0c5696e4b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_IntNumZeroSlot_hypotheses_example_79ecb2ebf4ba
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_MixedDiffConst_hypotheses_example_652314d4875e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PolyOfDiffs_hypotheses_example_ad7ad2c3722d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_ProductWithProjectiveSpace_hypotheses_example_bd159c78b846
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_ProjectionFormulaContracted_hypotheses_example_9fbe5bc3ae39
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_ProjectionFormulaDegree_hypotheses_example_2d68edfc775d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_contractPrime_bot_230ea120a67d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_coordinate_isMultiHomog_e8b5927ae14d


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
open Classical
namespace GroundTheory.Heights₂.Heights.FieldNumbers
namespace DivPushForward
theorem _root_.solution :
    let P' : Ideal (MRing (addBlock (ProjIdx 1) 0) ℚ) := ⊥
    let N : Ideal (MRing (fun k => addBlock (ProjIdx 1) 0 ((Function.Embedding.some : Unit ↪ Option Unit) k)) ℚ) → ℤ := fun _ => 1
    let N' : Ideal (MRing (addBlock (ProjIdx 1) 0) ℚ) → ℤ := fun W' =>
      if h : W'.IsPrime ∧ relDim (contractPrime (Function.Embedding.some : Unit ↪ Option Unit) W') = ((0 : ℕ) : WithBot (WithTop ℤ)) then
        haveI := h.1; (relDeg (Function.Embedding.some : Unit ↪ Option Unit) W' : ℤ) * N (contractPrime (Function.Embedding.some : Unit ↪ Option Unit) W') else 0
    IsMultiProjPrime P' ∧ relDim P' = ((0 + 1 : ℕ) : WithBot (WithTop ℤ)) ∧
      relDim (contractPrime (Function.Embedding.some : Unit ↪ Option Unit) P') = ((0 + 1 : ℕ) : WithBot (WithTop ℤ)) ∧
      IsMultiHomog (X ⟨(), (0 : Fin 2)⟩ : MRing (fun k => addBlock (ProjIdx 1) 0 ((Function.Embedding.some : Unit ↪ Option Unit) k)) ℚ)
        (blockWeight (ProjIdx 1) ⟨(), 0⟩) ∧
      (X ⟨(), (0 : Fin 2)⟩ : MRing (fun k => addBlock (ProjIdx 1) 0 ((Function.Embedding.some : Unit ↪ Option Unit) k)) ℚ) ∉ contractPrime (Function.Embedding.some : Unit ↪ Option Unit) P' ∧
      (∀ W' (hW' : IsMultiProjPrime W'), relDim W' = ((0 : ℕ) : WithBot (WithTop ℤ)) →
        relDim (contractPrime (Function.Embedding.some : Unit ↪ Option Unit) W') = ((0 : ℕ) : WithBot (WithTop ℤ)) →
        haveI := hW'.isPrime
        N' W' = relDeg (Function.Embedding.some : Unit ↪ Option Unit) W' * N (contractPrime (Function.Embedding.some : Unit ↪ Option Unit) W')) ∧
      (∀ W', IsMultiProjPrime W' → relDim W' = ((0 : ℕ) : WithBot (WithTop ℤ)) →
        relDim (contractPrime (Function.Embedding.some : Unit ↪ Option Unit) W') < ((0 : ℕ) : WithBot (WithTop ℤ)) → N' W' = 0) := by
  intro P' N N'
  obtain ⟨h1, h2, h3⟩ := ProjectionFormulaDegree.hypotheses_example
  refine ⟨h1, h2, h3, coordinate_isMultiHomog 1 0, ?_, ?_, ?_⟩
  · rw [show P' = ⊥ from rfl, contractPrime_bot, Ideal.mem_bot]
    exact X_ne_zero _
  · intro W' hW' _ hc
    show (if h : _ then _ else _) = _
    rw [dif_pos ⟨hW'.isPrime, hc⟩]
  · intro W' _ _ hc
    show (if h : _ then _ else _) = _
    rw [dif_neg (fun h => (ne_of_lt hc) h.2)]
end DivPushForward
end GroundTheory.Heights₂.Heights.FieldNumbers
