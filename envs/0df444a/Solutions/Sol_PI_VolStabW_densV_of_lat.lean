-- Prove2me | solution 1 for PI.VolStabW.densV_of_lat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:19:52.852635+00:00
-- url     : https://prove2.me/submissions/cf3b745c-4aff-4fa1-b07a-c26f79a34348

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensVSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_PosNear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensVNA
import Theorems.Thm_PI_VolStabW_tensNA_holds
import Theorems.Thm_PI_VolStabW_densVLC_of_lat
import Theorems.Thm_PI_VolStabW_densV_of


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
  Topology Filter
open scoped TensorProduct
namespace PI.VolStabW
theorem _root_.solution (hT : TensAll) (hC : DensVLat) : DensV :=
  densV_of hT tensNA_holds (densVLC_of_lat hT hC)
end PI.VolStabW
