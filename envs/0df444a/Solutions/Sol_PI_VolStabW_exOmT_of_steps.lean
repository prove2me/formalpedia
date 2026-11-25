-- Prove2me | solution 1 for PI.VolStabW.exOmT_of_steps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:17:57.697515+00:00
-- url     : https://prove2.me/submissions/0d1c2294-cb40-4ec6-9e69-c94f6744c2cf

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RestrProd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_SWeqOm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocExOf
import Theorems.Thm_PI_VolStabW_multFib_of
import Theorems.Thm_PI_VolStabW_fibPin_of
import Theorems.Thm_PI_VolStabW_locEx_of
import Theorems.Thm_PI_VolStabW_exOmT_of


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
theorem _root_.solution (hI : FibInfEx) (hV : FibVEx) (hL : LatSB) (hU : SdUniq)
    (hDI : DensFibInf) (hDV : DensFibV) (hR : RestrProd) : ExOmT :=
  exOmT_of (locEx_of hI hV hL) hU (fibPin_of hDI hDV hL) (multFib_of hDV) hR
end PI.VolStabW
