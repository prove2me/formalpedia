-- Prove2me | solution 1 for PI.VolStabSW.exOmT_of_steps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:53:31.545045+00:00
-- url     : https://prove2.me/submissions/b631519b-5cb5-48f9-b381-ff5a71c67861

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_RestrProd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_SWeqOm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocExOf
import Theorems.Thm_PI_VolStabSW_multFib_of
import Theorems.Thm_PI_VolStabSW_fibPin_of
import Theorems.Thm_PI_VolStabSW_locEx_of
import Theorems.Thm_PI_VolStabSW_exOmT_of


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
open scoped TensorProduct
namespace PI.VolStabSW
theorem _root_.solution (hI : FibInfEx) (hV : FibVEx) (hL : LatSB) (hU : SdUniq)
    (hDI : DensFibInf) (hDV : DensFibV) (hR : RestrProd) : ExOmT :=
  exOmT_of (locEx_of hI hV hL) hU (fibPin_of hDI hDV hL) (multFib_of hDV) hR
end PI.VolStabSW
