-- Prove2me | solution 1 for PI.VolStabW.measOrb_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:24:12.662535+00:00
-- url     : https://prove2.me/submissions/08ad4ffd-9205-4842-b1c1-e2e8a0813e02

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TopoAF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_MeasOrbSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_PosNear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TopoMeas
import Theorems.Thm_PI_VolStabW_TopoMeas_measurable_adm
import Theorems.Thm_PI_VolStabW_PositiveNearLattice_continuous_orbit


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
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField MeasureTheory PI.VolFromSW
namespace PI.VolStabW
theorem _root_.solution : MeasOrb := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet Φ hΦ
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  exact (TopoMeas.measurable_adm Φ hΦ).comp
    (PositiveNearLattice.continuous_orbit σ J (ratTup (AF F) X0)).measurable
end PI.VolStabW
