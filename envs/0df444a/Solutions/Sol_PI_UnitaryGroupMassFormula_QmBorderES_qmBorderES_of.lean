-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmBorderES.qmBorderES_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:19:07.550608+00:00
-- url     : https://prove2.me/submissions/d047f5af-2d65-48e4-a75e-6b18e694940c

import Definitions.Def_Formalism_PeriodIntegrals_QmBorderES
import Definitions.Def_Formalism_PeriodIntegrals_QmColExp
import Definitions.Def_Formalism_PeriodIntegrals_QmRowExp
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BorderSignIdentity_SkipOneEqSuccAbove
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderES_borderE_of
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderES_borderS_of

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Formalism.REAL
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.QmBorderES
namespace PI.UnitaryGroupMassFormula.QmBorderES
theorem _root_.solution (h1 : PI.QmColExp) (h2 : PI.QmRowExp) : PI.QmBorderES :=
  ⟨borderE_of h1.1 h2.2, borderS_of h1.2 h2.1⟩
end PI.UnitaryGroupMassFormula.QmBorderES
