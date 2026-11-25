-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_FlagIntegralProportional_intersectionNumber_baseChange_171f006c2d43
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:32:13.871828+00:00
-- url     : https://prove2.me/submissions/a2eea3b9-e4d1-4e0c-a189-432236ed75e1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsFlag
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_IsFlagIntegralOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagIntegralRealEqMulDdConst
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCoinvAtTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCoinvPolynomialReduction
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCoinvMonomialReduction
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCoinvStepReduction
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCoinvIdealComponent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCoinvIdealRepresentation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PHomogeneousComponentMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCoinvStaircaseComponent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCoinvStaircaseDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StaircaseIsHomogeneous
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_CoinvAtTop_closed_81de5cc3444c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_FlagProportional_eval_top_e1c72c19af4e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_ddConst_monomial_rho_bbfe7514f1e2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_ddConst_psumAt_mul_5fb3aa7ed198
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_rho_degree_cfc9f82bd5ec


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset
noncomputable section
open FlagProportional
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace FlagIntegralProportional
theorem _root_.solution : IndefiniteRowSideFullHecke.RestTerms.FlagIntegralProportional.Statement := by
  intro f j k _ _ _ I hI
  set s : IndefiniteRowSideFullHecke.RestTerms.Roots f j k := monomial (Coinv.staircase f (j + k)) 1
  have hdd : ∀ G : IndefiniteRowSideFullHecke.RestTerms.Roots f j k, G.IsHomogeneous (IndefiniteRowSideFullHecke.RestTerms.dimFl f j k) →
      ∃ c : ℝ, I G = c * I s ∧ IndefiniteRowSideFullHecke.RestTerms.ddConst f j k G = c * IndefiniteRowSideFullHecke.RestTerms.ddConst f j k s := by
    intro G hG
    obtain ⟨c, hc⟩ := CoinvAtTop.closed ℝ f (j + k) G hG
    exact ⟨c, eval_top f j k I hI.kills G hG c hc,
      eval_top f j k (IndefiniteRowSideFullHecke.RestTerms.ddConst f j k)
        (fun m τ G hm _ _ => FlagEq.ddConst_psumAt_mul f j k m τ G hm) G hG c hc⟩
  have hs0 : IndefiniteRowSideFullHecke.RestTerms.ddConst f j k s ≠ 0 := by
    obtain ⟨c, -, h⟩ := hdd (monomial (FlagEq.rho f (j + k)) 1)
      (isHomogeneous_monomial _ (by rw [FlagEq.rho_degree]; rfl))
    rw [FlagEq.ddConst_monomial_rho] at h
    intro h0
    rw [h0, mul_zero] at h
    exact one_ne_zero h
  have hIs : I s ≠ 0 := by
    obtain ⟨G0, hG0, hne⟩ := hI.ne_zero
    obtain ⟨c, h, -⟩ := hdd G0 hG0
    intro h0
    rw [h0, mul_zero] at h
    exact hne h
  refine ⟨I s / IndefiniteRowSideFullHecke.RestTerms.ddConst f j k s, div_ne_zero hIs hs0, fun G hG => ?_⟩
  obtain ⟨c, h1, h2⟩ := hdd G hG
  rw [h1, h2]
  field_simp
end FlagIntegralProportional
end GroundTheory.Heights₂.Heights.RestTerms
