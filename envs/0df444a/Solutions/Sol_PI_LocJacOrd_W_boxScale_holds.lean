-- Prove2me | solution 1 for PI.LocJacOrd.W.boxScale_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:21:44.246042+00:00
-- url     : https://prove2.me/submissions/5c3ac2f5-b1dc-4165-a4ff-55dd2f162da3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianOrder_LocJacOrdOfSd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_SdNormHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_KitScale
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianOrder_LocJacOrdClosed
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_boxScale


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LocJacOrd PI.LocJacOrd.W
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain
namespace PI.LocJacOrd.W
theorem _root_.solution : BoxScale := by
  intro F E _ _ _ _ _ v ι _ hfin μ _ x hx
  exact PI.UnitaryGroupMassFormula.LocJacTyp.boxScale v hfin μ x hx
end PI.LocJacOrd.W
