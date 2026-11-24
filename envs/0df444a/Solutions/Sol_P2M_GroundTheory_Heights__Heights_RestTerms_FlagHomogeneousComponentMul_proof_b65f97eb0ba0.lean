-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_FlagHomogeneousComponentMul_proof_b65f97eb0ba0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:08:32.038838+00:00
-- url     : https://prove2.me/submissions/89357e87-66af-4fd7-a19c-1e48cb63d220

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsFlag
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PHomogeneousComponentMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PFlagHomogeneousComponentMul
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_HomogeneousComponentMul_proof_071fefd82e0b


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
open MvPolynomial
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace FlagHomogeneousComponentMul
theorem _root_.solution : FlagHomogeneousComponentMul.Statement := by
  intro σ P G k n hP
  exact HomogeneousComponentMul.proof σ ℚ P G k n hP
end FlagHomogeneousComponentMul
end GroundTheory.Heights₂.Heights.RestTerms
