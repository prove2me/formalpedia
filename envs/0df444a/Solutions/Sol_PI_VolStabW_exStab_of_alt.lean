-- Prove2me | solution 1 for PI.VolStabW.exStab_of_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:19:25.814013+00:00
-- url     : https://prove2.me/submissions/119c7f52-37e0-4209-bd1c-4442ab91fc5c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_ExStabSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_ExStabTop
import Theorems.Thm_PI_VolStabW_stabClosed_holds
import Theorems.Thm_PI_VolStabW_secCtblG_of
import Theorems.Thm_PI_VolStabW_orbEmb_of
import Theorems.Thm_PI_VolStabW_exStab_of


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
theorem _root_.solution (hW : SecCtblW) (hP : LCSCPolish) (hO : OrbTup) (hH : StabUni) (hI : NuInv)
    (hF : NuFin) (hN : NuNeZero) (hU : Unimod) : ExStab :=
  exStab_of (secCtblG_of hW) hO stabClosed_holds hH hI hF hN (orbEmb_of hW hP) hU
end PI.VolStabW
