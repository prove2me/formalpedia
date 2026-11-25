-- Prove2me | solution 1 for PI.VolSemiDirect.W.Cj.gl_generated_transvections_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:25:11.099403+00:00
-- url     : https://prove2.me/submissions/b6202424-6d3a-4486-8adb-7277bffcf3c7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_CjDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_GlGeneratedTransvectionsDiag
import Theorems.Thm_PI_VolSemiDirect_W_Cj_reduce

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolSemiDirect PI.VolSemiDirect.W PI.VolSemiDirect.W.Cj
open Matrix
namespace PI.VolSemiDirect.W.Cj
theorem _root_.solution : ElimSR1 := by
  intro A _ hA k X
  exact reduce hA k X (by
    intro i j h
    exfalso
    omega)
end PI.VolSemiDirect.W.Cj
