-- Prove2me | solution 1 for PI.VolStabW.restrProd_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:50:59.926477+00:00
-- url     : https://prove2.me/submissions/1722baa9-e0c0-4eb1-ae38-61136c8c8797

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RestrProdSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RestrProdA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RestrProdG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_FiniteOnCompacts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RPGlue
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RpAbsHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RestrProdAlt
import Theorems.Thm_PI_VolStabW_RestrProdA_latCofin_holds
import Theorems.Thm_PI_VolStabW_RestrProdA_rpTail_holds
import Theorems.Thm_PI_VolStabW_RestrProdG_rpGram_holds
import Theorems.Thm_PI_VolStabW_restrProd_of
import Theorems.Thm_PI_VolStabW_rpAbs_holds
import Theorems.Thm_PI_VolStabW_rpFib_holds
import Theorems.Thm_PI_VolStabW_rpGlue_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.VolStabW
namespace PI.VolStabW
theorem _root_.solution : RestrProd :=
  restrProd_of rpAbs_holds rpFib_holds rpGlue_holds RestrProdG.rpGram_holds
    RestrProdA.rpTail_holds RestrProdA.latCofin_holds
end PI.VolStabW
