-- Prove2me | solution 1 for PIW.HCFdeg.stBdd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:01:40.678878+00:00
-- url     : https://prove2.me/submissions/704b4717-e940-46c5-9ff0-79555d6751ae

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_FormalDegreeFromOrthogonality
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_ContinuousToL2Map
import Theorems.Thm_PIW_HCFdeg_toL2Map_apply_ae_eq
import Theorems.Thm_PIW_HCFdeg_continuous_toL2Map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.HCFdeg
open MeasureTheory Filter Topology
namespace PIW.HCFdeg
theorem _root_.solution : StBdd := by
  intro X H _ μ _ _ _ c hcont hL
  exact ⟨⟨toL2Map c hL, continuous_toL2Map c hcont hL⟩, toL2Map_apply_ae_eq c hL⟩
end PIW.HCFdeg
