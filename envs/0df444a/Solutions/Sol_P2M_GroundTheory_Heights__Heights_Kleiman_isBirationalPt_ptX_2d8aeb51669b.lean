-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_isBirationalPt_ptX_2d8aeb51669b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:02:43.942672+00:00
-- url     : https://prove2.me/submissions/1810c639-e426-46ae-8d9c-13dcbfcf6e7a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_AlgebraMapMemChartRingLine
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_ptX_ne_zero_891cc935a1a3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_mem_chartRing_ptX_e1c6bdba4be9

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Filter
noncomputable section
universe u v w
variable (k : Type u) [Field k]
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution : IsBirationalPt k (ptX k) := fun s =>
  ⟨singleChart (ptX_ne_zero k 0), s, 1, mem_chartRing_ptX k _ s, mem_chartRing_ptX k _ 1, one_ne_zero,
    mul_one s⟩
end GroundTheory.Heights₂.Heights.Kleiman
