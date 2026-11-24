-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_TermBoundEq_coeff_coeffMap_90caddac2fb8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:08:39.364725+00:00
-- url     : https://prove2.me/submissions/8aa95a37-c6a6-4024-8c37-81db3774a9b0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_IsPowerSumDecompositionHomogeneousComponent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagIntegralRealEqMulDdConst
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagIntegralRealRootRingToRealAlt
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_C_43a59c7a9997
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_X_6be993a34174
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_C_43a59c7a9997
attribute [local simp] P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_X_6be993a34174



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset
noncomputable section
open GroundTheory.Heights₂.Heights.RestTerms.TermBoundEq
variable {σ : Type*} (φ : Module.Dual ℚ ℝ)
namespace GroundTheory.Heights₂.Heights.RestTerms.TermBoundEq
theorem _root_.solution (P : MvPolynomial σ ℝ) (d : σ →₀ ℕ) :
    coeff d (coeffMap φ P) = φ (coeff d P) := by
  classical
  rw [coeffMap, coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with hd
  · rfl
  · rw [notMem_support_iff.1 hd, map_zero]
end GroundTheory.Heights₂.Heights.RestTerms.TermBoundEq
