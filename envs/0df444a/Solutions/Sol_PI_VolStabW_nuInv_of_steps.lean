-- Prove2me | solution 1 for PI.VolStabW.nuInv_of_steps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:09:51.461713+00:00
-- url     : https://prove2.me/submissions/bdefaa5e-5c98-4a4f-b20f-ee532fdbd156

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_PullLocSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TopoGram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RestrProd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TopoFibInv
import Theorems.Thm_PI_VolStabW_fibInvInf_of
import Theorems.Thm_PI_VolStabW_fibInvV_of
import Theorems.Thm_PI_VolStabW_gramPres_holds
import Theorems.Thm_PI_VolStabW_nuInv_of_loc
import Theorems.Thm_PI_VolStabW_pullLoc_of


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
open scoped TensorProduct
namespace PI.VolStabW
theorem _root_.solution (hD : DetAdm) (hC : CompG) (hP : FibPin) (hMI : MuInvInf) (hMV : MuInvV) :
    NuInv :=
  nuInv_of_loc gramPres_holds (pullLoc_of hC (fibInvInf_of hP hMI) (fibInvV_of hP hMV)) hD
end PI.VolStabW
