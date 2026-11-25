-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_ptX_ne_zero_891cc935a1a3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:27:05.297899+00:00
-- url     : https://prove2.me/submissions/54a6dadf-df6b-4e24-bbde-a2cfbd4c5154

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_AlgebraMapMemChartRingLine

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
theorem _root_.solution (i : Fin (0 + 1)) : ptX k i ≠ 0 := one_ne_zero
end GroundTheory.Heights₂.Heights.Kleiman
