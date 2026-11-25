-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_DividedDifferenceVandermonde_flagIntegral_eq_mul_ddConst_53ddae8e92d5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:07:25.741225+00:00
-- url     : https://prove2.me/submissions/6f7a713d-2fe7-4ecc-b0eb-d98d09db0bbd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_IsFlagIntegralOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_IsPowerSumDecompositionHomogeneousComponent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagIntegralRealEqMulDdConst
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_AntisymmetrizeBlockVandermondeOf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_DividedDifferenceVandermonde_ringToReal_eq_map_47d90c7e561f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_flagIntegralReal_eq_mul_ddConst_cd95a7f5162d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_flagIntegralReal_map_68b8ee4ccd2f


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
open GroundTheory.Heights₂.Heights.RestTerms.DividedDifferenceVandermonde
namespace GroundTheory.Heights₂.Heights.RestTerms.DividedDifferenceVandermonde
theorem _root_.solution (f N j k : ℕ) (h : N = j + k) (Φ : RootRing f N) :
    (flagIntegral f N Φ : ℝ) =
      FlagEq.stairConst f (j + k) * IndefiniteRowSideFullHecke.RestTerms.ddConst f j k (rootRingToReal f N j k h Φ) := by
  subst h
  rw [← flagIntegralReal_map, flagIntegralReal_eq_mul_ddConst, ringToReal_eq_map]
end GroundTheory.Heights₂.Heights.RestTerms.DividedDifferenceVandermonde
