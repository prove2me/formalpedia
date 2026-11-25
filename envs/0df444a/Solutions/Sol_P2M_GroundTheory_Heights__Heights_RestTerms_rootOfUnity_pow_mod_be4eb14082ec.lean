-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_rootOfUnity_pow_mod_be4eb14082ec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:29:21.393308+00:00
-- url     : https://prove2.me/submissions/5c130f9f-0923-4b92-98ca-44366167d2e2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsSchur
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSchRootOfUnityRowsEq
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_rootOfUnity_pow_self_c1a38c4d33f2

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
theorem _root_.solution (k : ℕ) (hk : k ≠ 0) (a : ℕ) :
    rootOfUnity k ^ a = rootOfUnity k ^ (a % k) := by
  conv_lhs => rw [← Nat.mod_add_div a k, pow_add, pow_mul, rootOfUnity_pow_self k hk, one_pow,
    mul_one]
end GroundTheory.Heights₂.Heights.RestTerms
