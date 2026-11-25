-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_TermBoundEq_coeffMap_sum_93079432c036
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:52:55.296875+00:00
-- url     : https://prove2.me/submissions/4261fab3-048a-48bb-9c52-0b511955722a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_IsPowerSumDecompositionHomogeneousComponent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagIntegralRealEqMulDdConst
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagIntegralRealRootRingToRealAlt
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_TermBoundEq_coeff_coeffMap_90caddac2fb8
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
theorem _root_.solution {ι : Type*} (s : Finset ι) (P : ι → MvPolynomial σ ℝ) :
    coeffMap φ (∑ i ∈ s, P i) = ∑ i ∈ s, coeffMap φ (P i) := by
  ext d
  simp only [coeff_coeffMap, coeff_sum, map_sum]
end GroundTheory.Heights₂.Heights.RestTerms.TermBoundEq
