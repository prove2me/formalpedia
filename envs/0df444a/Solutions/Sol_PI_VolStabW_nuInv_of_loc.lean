-- Prove2me | solution 1 for PI.VolStabW.nuInv_of_loc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:03:54.678816+00:00
-- url     : https://prove2.me/submissions/7cea33ce-5724-4633-95d4-7c86468917c1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_NuInvSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TopoMeas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_NuInvLoc
import Theorems.Thm_PI_VolStabW_omInv_of
import Theorems.Thm_PI_VolStabW_nuInv_of
import Theorems.Thm_PI_VolStabW_omUniq_of


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
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct ENNReal
namespace PI.VolStabW
theorem _root_.solution (hG : GramPres) (hP : PullLoc) (hD : DetAdm) : NuInv :=
  nuInv_of (omUniq_of hD) (omInv_of hG hP)
end PI.VolStabW
