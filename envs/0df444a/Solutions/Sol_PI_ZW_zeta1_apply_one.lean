-- Prove2me | solution 1 for PI.ZW.zeta1_apply_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:24:33.396648+00:00
-- url     : https://prove2.me/submissions/8e936f6e-f01f-48fc-af92-bb5d692ecc4d

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
theorem _root_.solution : zeta1 1 = 1 := by
  show DirichletCharacter.LFunctionTrivChar₁ 1 1 = 1
  unfold DirichletCharacter.LFunctionTrivChar₁
  simp
end PI.ZW
