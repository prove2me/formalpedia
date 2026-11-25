-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_rootOfUnity_pow_self_c1a38c4d33f2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:14:18.037512+00:00
-- url     : https://prove2.me/submissions/6db7616a-4349-4b67-92a8-e70cfbe9fb43

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsSchur
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSchRootOfUnityRowsEq

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
open Complex
namespace GroundTheory.Heights₂.Heights.RestTerms
theorem _root_.solution (k : ℕ) (hk : k ≠ 0) : rootOfUnity k ^ k = 1 :=
  (Complex.isPrimitiveRoot_exp k hk).pow_eq_one
end GroundTheory.Heights₂.Heights.RestTerms
