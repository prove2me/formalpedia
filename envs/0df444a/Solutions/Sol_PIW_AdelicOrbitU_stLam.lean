-- Prove2me | solution 1 for PIW.AdelicOrbitU.stLam
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:09:32.172419+00:00
-- url     : https://prove2.me/submissions/46327140-7718-462e-b66d-eea2f51f659e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_UnitChoice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_QuadFiniteDimensional
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_StLamOf
import Theorems.Thm_PIW_AdelicOrbitU_stLam_of
import Theorems.Thm_PIW_AdelicOrbitU_quadGen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.AdelicOrbitU
namespace PIW.AdelicOrbitU
theorem _root_.solution : StLam := stLam_of quadGen
end PIW.AdelicOrbitU
