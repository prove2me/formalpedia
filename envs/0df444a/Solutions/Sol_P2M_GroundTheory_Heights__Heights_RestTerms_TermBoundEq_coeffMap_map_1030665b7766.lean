-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_TermBoundEq_coeffMap_map_1030665b7766
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:52:39.903036+00:00
-- url     : https://prove2.me/submissions/991936c0-b9d0-438a-bd0f-94d806ccee46

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_IsPowerSumDecompositionHomogeneousComponent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagIntegralRealEqMulDdConst
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagIntegralRealRootRingToRealAlt
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_TermBoundEq_coeff_coeffMap_90caddac2fb8

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
open GroundTheory.Heights₂.Heights.RestTerms.TermBoundEq
variable {σ : Type*} (φ : Module.Dual ℚ ℝ)
namespace GroundTheory.Heights₂.Heights.RestTerms.TermBoundEq
theorem _root_.solution (R : MvPolynomial σ ℚ) :
    coeffMap φ (map (algebraMap ℚ ℝ) R) = φ 1 • R := by
  ext d
  rw [coeff_coeffMap, coeff_map, coeff_smul, smul_eq_mul, ← mul_one (algebraMap ℚ ℝ _),
    ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
end GroundTheory.Heights₂.Heights.RestTerms.TermBoundEq
