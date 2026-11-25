-- Prove2me | solution 1 for PI.VolStabW.densV_of_filt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:27:39.31732+00:00
-- url     : https://prove2.me/submissions/e167912c-06a9-4cd5-89f0-d9402973d7d0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensVNA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensVGlue
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TensTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensVCore
import Theorems.Thm_PI_VolStabW_densVLat_of
import Theorems.Thm_PI_VolStabW_densV_of_lat


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
  Topology
open scoped TensorProduct
namespace PI.VolStabW
theorem _root_.solution (hP1 : HenselCount) (hP2 : CosDens) (hT : TensAll) (hF : GramFilt) :
    DensV :=
  densV_of_lat hT (densVLat_of hP1 hP2 hT hF)
end PI.VolStabW
