-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComplexSets_coneEq_ne_zero_df5d0619dfe6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:10:30.172287+00:00
-- url     : https://prove2.me/submissions/fa1f30f5-1bad-4fb0-9430-b64e475813ae

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_coneEq_prime_b18251f83221

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open MvPolynomial Pointwise
noncomputable section
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.ComplexSets
theorem _root_.solution : coneEq ≠ 0 := coneEq_prime.ne_zero
end GroundTheory.Heights₂.Heights.ComplexSets
