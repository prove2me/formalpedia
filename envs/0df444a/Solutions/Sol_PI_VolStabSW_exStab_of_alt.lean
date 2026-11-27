-- Prove2me | solution 1 for PI.VolStabSW.exStab_of_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:18:06.556931+00:00
-- url     : https://prove2.me/submissions/48ec2489-3a1f-422a-9520-40b79a456b81

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_ExStabSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_ExStabTop
import Theorems.Thm_PI_VolStabSW_stabClosed_holds
import Theorems.Thm_PI_VolStabSW_secCtblG_of
import Theorems.Thm_PI_VolStabSW_orbEmb_of
import Theorems.Thm_PI_VolStabSW_exStab_of


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
open scoped TensorProduct ENNReal
namespace PI.VolStabSW
theorem _root_.solution (hW : SecCtblW) (hP : LCSCPolish) (hO : OrbTup) (hH : StabUni) (hI : NuInv)
    (hF : NuFin) (hN : NuNeZero) (hU : Unimod) : ExStab :=
  exStab_of (secCtblG_of hW) hO stabClosed_holds hH hI hF hN (orbEmb_of hW hP) hU
end PI.VolStabSW
