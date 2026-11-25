-- Prove2me | solution 1 for PI.VolStabSW.densV_of_filt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:58:49.364882+00:00
-- url     : https://prove2.me/submissions/1788d701-065f-40e6-9ca5-11b551c74dca

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensVNA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensVGlue
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TensTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensVCore
import Theorems.Thm_PI_VolStabSW_densVLat_of
import Theorems.Thm_PI_VolStabSW_densV_of_lat


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
  Topology
open scoped TensorProduct
namespace PI.VolStabSW
theorem _root_.solution (hP1 : HenselCount) (hP2 : CosDens) (hT : TensAll) (hF : GramFilt) :
    DensV :=
  densV_of_lat hT (densVLat_of hP1 hP2 hT hF)
end PI.VolStabSW
