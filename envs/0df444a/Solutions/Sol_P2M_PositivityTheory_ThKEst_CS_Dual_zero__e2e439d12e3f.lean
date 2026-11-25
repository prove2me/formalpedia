-- Prove2me | solution 1 for P2M_PositivityTheory_ThKEst_CS_Dual_zero__e2e439d12e3f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:51:18.874691+00:00
-- url     : https://prove2.me/submissions/ce23246f-c45e-4944-a752-e59a36620e65

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_FrameEstimates_CoefSumA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Topology Filter
open scoped ENNReal ComplexConjugate Pointwise
open PositivityTheory PositivityTheory.ThKEst PositivityTheory.ThKEst.CS
variable {G Γ : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [AddCommGroup Γ]
variable {r : Γ →+ G} {e : Γ → G → ℂ}
omit [IsTopologicalAddGroup G]
namespace PositivityTheory.ThKEst.CS
namespace Dual
theorem _root_.solution (h : Dual r e) (ξ) : e ξ 0 = 1 := by
  simpa using h.triv ξ 0
end Dual
end PositivityTheory.ThKEst.CS
