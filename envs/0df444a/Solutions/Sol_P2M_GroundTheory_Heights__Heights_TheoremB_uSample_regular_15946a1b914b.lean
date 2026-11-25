-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TheoremB_uSample_regular_15946a1b914b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:22:26.827818+00:00
-- url     : https://prove2.me/submissions/8fc0930e-07ca-434f-8647-669cf61b7a7a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MultinomialWeights_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MultinomialWeights_StatementsEnd

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
theorem _root_.solution : IsRegular d1 (uR d1 uSample) := by
  intro τ a b hab
  have hb2 : b.val < 2 := b.isLt
  have ha : a.val = 0 := by omega
  have hb : b.val = 1 := by omega
  simp [uR, uSample, ha, hb]
end GroundTheory.Heights₂.Heights.TheoremB
