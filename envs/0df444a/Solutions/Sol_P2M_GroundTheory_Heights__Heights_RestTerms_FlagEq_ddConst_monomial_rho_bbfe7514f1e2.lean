-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_ddConst_monomial_rho_bbfe7514f1e2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:24:29.164303+00:00
-- url     : https://prove2.me/submissions/ab099891-62c2-4d11-8675-52367327f1df

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_CoeffRenameProdCongrRight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagIntegralRealEqMulDdConst
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_ddConst_eq_c1a45b54fd72
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_eq_one_of_stairExp_eq_fc1e9a82e37f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_permSign_one_c2a06108d15d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_stairExp_one_99b60d1affe7


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
open GroundTheory.Heights₂.Heights.RestTerms.FlagEq
namespace GroundTheory.Heights₂.Heights.RestTerms.FlagEq
theorem _root_.solution (f j k : ℕ) :
    IndefiniteRowSideFullHecke.RestTerms.ddConst f j k (monomial (rho f (j + k)) (1 : ℝ)) = 1 := by
  rw [ddConst_eq, Fintype.sum_eq_single 1]
  · simp [stairExp_one, permSign_one]
  · intro w hw
    rw [coeff_monomial, if_neg (fun h => hw (eq_one_of_stairExp_eq w h.symm)), mul_zero]
end GroundTheory.Heights₂.Heights.RestTerms.FlagEq
