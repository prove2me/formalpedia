-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComplexSets_coneEq_prime_b18251f83221
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:26:54.650624+00:00
-- url     : https://prove2.me/submissions/ce6ae7a5-81c1-43d8-be1c-4b00e60d4118

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_coneEq_irreducible_5f02fbd10eb9

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
theorem _root_.solution : Prime coneEq := coneEq_irreducible.prime
end GroundTheory.Heights₂.Heights.ComplexSets
