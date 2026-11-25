-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_FlagProportional_staircase_isHomogeneous_713be1057cf7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:51:14.4378+00:00
-- url     : https://prove2.me/submissions/4bdc1aef-977b-4acf-a22b-32142d88cf1e

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
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Coinv_sum_staircase_exponents_9893f3414274


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
open GroundTheory.Heights₂.Heights.RestTerms.FlagProportional
namespace GroundTheory.Heights₂.Heights.RestTerms.FlagProportional
theorem _root_.solution (f j k : ℕ) :
    (monomial (Coinv.staircase f (j + k)) (1 : ℝ)).IsHomogeneous (IndefiniteRowSideFullHecke.RestTerms.dimFl f j k) := by
  refine isHomogeneous_monomial _ ?_
  rw [Finsupp.degree_eq_sum]
  show ∑ v, (Coinv.staircase f (j + k)) v = Coinv.coinvTop f (j + k)
  rw [← Coinv.sum_staircase_exponents]
  simp [Coinv.staircase]
end GroundTheory.Heights₂.Heights.RestTerms.FlagProportional
