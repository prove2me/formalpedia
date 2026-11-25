-- Prove2me | solution 1 for PI.VolStabW.detAdm_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:22:19.94336+00:00
-- url     : https://prove2.me/submissions/ab88cdc1-3d6a-4394-9c8e-bc8463d1e950

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DetAdmC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_NuInvSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DetAdm
import Theorems.Thm_PI_VolStabW_DeterminantAdmissible_detAdm_gen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
namespace PI.VolStabW
theorem _root_.solution : DetAdm := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ν1 ν2 h1 h2 h
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  exact DeterminantAdmissible.detAdm_gen ν1 ν2 h1 h2 h
end PI.VolStabW
