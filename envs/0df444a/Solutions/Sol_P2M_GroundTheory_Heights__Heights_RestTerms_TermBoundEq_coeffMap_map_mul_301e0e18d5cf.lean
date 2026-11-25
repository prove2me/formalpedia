-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_TermBoundEq_coeffMap_map_mul_301e0e18d5cf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:52:54.481936+00:00
-- url     : https://prove2.me/submissions/a9a5a023-d6eb-4a55-81b5-b6487655ef2e

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
theorem _root_.solution (R : MvPolynomial σ ℚ) (P : MvPolynomial σ ℝ) :
    coeffMap φ (map (algebraMap ℚ ℝ) R * P) = R * coeffMap φ P := by
  classical
  ext d
  rw [coeff_coeffMap, coeff_mul, coeff_mul, map_sum]
  refine sum_congr rfl fun x _ => ?_
  rw [coeff_map, coeff_coeffMap, ← Algebra.smul_def, map_smul, smul_eq_mul]
end GroundTheory.Heights₂.Heights.RestTerms.TermBoundEq
