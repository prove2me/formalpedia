-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_SchRootOfUnityVandermondeNe_rootOfUnity_isPrimitiveRoot_6f2807b96c51
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:52:37.74146+00:00
-- url     : https://prove2.me/submissions/67168d0c-3f82-4a0a-91da-37377177779a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsSchur
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSchRootOfUnityVandermondeNe

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
open Finset
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace SchRootOfUnityVandermondeNe
theorem _root_.solution {k : ℕ} (hk : 1 ≤ k) : IsPrimitiveRoot (rootOfUnity k) k := by
  unfold rootOfUnity
  exact Complex.isPrimitiveRoot_exp k (by omega)
end SchRootOfUnityVandermondeNe
end GroundTheory.Heights₂.Heights.RestTerms
