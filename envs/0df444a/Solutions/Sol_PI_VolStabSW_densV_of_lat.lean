-- Prove2me | solution 1 for PI.VolStabSW.densV_of_lat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:51:30.530204+00:00
-- url     : https://prove2.me/submissions/283def33-b186-4329-a042-e931f7b2ded0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensVSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_PosNear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensVNA
import Theorems.Thm_PI_VolStabSW_tensNA_holds
import Theorems.Thm_PI_VolStabSW_densVLC_of_lat
import Theorems.Thm_PI_VolStabSW_densV_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
  Topology Filter
open scoped TensorProduct
namespace PI.VolStabSW
theorem _root_.solution (hT : TensAll) (hC : DensVLat) : DensV :=
  densV_of hT tensNA_holds (densVLC_of_lat hT hC)
end PI.VolStabSW
