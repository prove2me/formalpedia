-- Prove2me | solution 1 for PI.VolSemiDirect.W.Cj.trace_basis_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:08:55.874635+00:00
-- url     : https://prove2.me/submissions/05ef77e7-acf4-4e5e-b9fd-d578fc3d9c7b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_CjTDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ProjHA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_TraceGramNondegenerate
import Theorems.Thm_PI_VolSemiDirect_W_Cj_trace_one_tmul

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
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
open scoped TensorProduct
namespace PI.VolSemiDirect.W.Cj
theorem _root_.solution : TraceBase := by
  intro F E _ _ _ _ R _ _ σ M J x y
  rw [W.hR_ratV R σ J x y]
  exact trace_one_tmul R _
end PI.VolSemiDirect.W.Cj
