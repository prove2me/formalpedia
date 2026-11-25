-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartChoice_joinFirst_C_58f1c58d3e33
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:36:21.70535+00:00
-- url     : https://prove2.me/submissions/23bc0817-5a7d-4893-b691-83af5f260d84

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsSectionOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChowFormSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartChoice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ChartChoice
variable {F : Type} [Field F] {n e : ℕ}
namespace GroundTheory.Heights₂.Heights.ChartChoice
theorem _root_.solution (a : MvPolynomial (Fin e × Fin n) F) :
    joinFirst F e n (C a) = rename (shiftVar e n) a := by
  simp [joinFirst]
end GroundTheory.Heights₂.Heights.ChartChoice
