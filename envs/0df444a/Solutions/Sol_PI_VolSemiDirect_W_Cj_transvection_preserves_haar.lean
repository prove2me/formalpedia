-- Prove2me | solution 1 for PI.VolSemiDirect.W.Cj.transvection_preserves_haar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:58:45.371841+00:00
-- url     : https://prove2.me/submissions/37e0b4a2-e4b1-453a-8279-f907de220d6a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_CjDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_UniHaar
import Theorems.Thm_PI_VolSemiDirect_W_Cj_uni_haar
import Theorems.Thm_PI_VolSemiDirect_W_Cj_transvection_uni

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
open MeasureTheory
namespace PI.VolSemiDirect.W.Cj
theorem _root_.solution : TransvHaar := by
  intro A _ _ _ _ _ _ _ _ k i j hij c μ hμ
  haveI := hμ
  exact uni_haar k _ (transvection_uni i j hij c) μ
end PI.VolSemiDirect.W.Cj
