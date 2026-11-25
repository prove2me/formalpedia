-- Prove2me | solution 1 for PI.ZW.analyticAt_riemannZeta_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:23:42.394426+00:00
-- url     : https://prove2.me/submissions/181e270d-9e5e-45b8-a460-ba15177c4bf8

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroWindow_RightChi
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroWindow_RightOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Metric Complex Filter Topology
open PI PI.ZW
namespace PI.ZW
theorem _root_.solution {s : ℂ} (hs : s ≠ 1) : AnalyticAt ℂ riemannZeta s := by
  exact DifferentiableOn.analyticAt (fun z hz => (differentiableAt_riemannZeta hz).differentiableWithinAt)
    (isOpen_compl_singleton.mem_nhds hs)
end PI.ZW
