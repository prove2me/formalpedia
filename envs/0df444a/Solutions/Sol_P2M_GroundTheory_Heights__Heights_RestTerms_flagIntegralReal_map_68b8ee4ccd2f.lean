-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_flagIntegralReal_map_68b8ee4ccd2f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:50:11.822608+00:00
-- url     : https://prove2.me/submissions/91443b73-f210-44e2-9e24-f3c9b4154618

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_CoeffRenameProdCongrRight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagIntegralRealEqMulDdConst

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
namespace GroundTheory.Heights₂.Heights.RestTerms
theorem _root_.solution (f N : ℕ) (Φ : RootRing f N) :
    flagIntegralReal f N (map (algebraMap ℚ ℝ) Φ) = (flagIntegral f N Φ : ℝ) := by
  simp [flagIntegralReal, flagIntegral, coeff_map, Finsupp.prod]
end GroundTheory.Heights₂.Heights.RestTerms
