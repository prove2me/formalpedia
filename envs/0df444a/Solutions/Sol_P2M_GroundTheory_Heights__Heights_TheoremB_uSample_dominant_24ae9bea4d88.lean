-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TheoremB_uSample_dominant_24ae9bea4d88
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:29:36.8887+00:00
-- url     : https://prove2.me/submissions/16fa8796-725e-4be3-b537-3237447debe8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MultinomialWeights_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MultinomialWeights_StatementsEnd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TheoremB_uSample_regular_15946a1b914b

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.TheoremB
open MvPolynomial Finset Filter Topology
variable (d : IndexData)
variable {d}
namespace GroundTheory.Heights₂.Heights.TheoremB
theorem _root_.solution : IsDominant d1 (uR d1 uSample) :=
  fun τ a b hab => (uSample_regular τ a b hab).le
end GroundTheory.Heights₂.Heights.TheoremB
