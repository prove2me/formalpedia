-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_blockPowerSum_isHomogeneous_c5d784bee3b6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:12:01.378444+00:00
-- url     : https://prove2.me/submissions/39c573ad-3a5c-4113-9f7f-dd5f2b18591e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_IsFlagIntegralOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PHomogeneousComponentMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_IsPowerSumDecompositionHomogeneousComponent

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
theorem _root_.solution (f N m : ℕ) (τ : Fin f) :
    (blockPowerSum f N m τ).IsHomogeneous m :=
  IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_X_pow _ _
end GroundTheory.Heights₂.Heights.RestTerms
