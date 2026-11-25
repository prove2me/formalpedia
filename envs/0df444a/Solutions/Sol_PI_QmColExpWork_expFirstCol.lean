-- Prove2me | solution 1 for PI.QmColExpWork.expFirstCol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:06:45.601214+00:00
-- url     : https://prove2.me/submissions/8f8bda05-2e26-4f0e-b142-b0d3b2ae29b1

import Definitions.Def_Formalism_PeriodIntegrals_QmColExp
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialFirstColumn_FirstColumnSplitBijective
import Theorems.Thm_PI_QmColExpWork_expFirst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open PI PI.QmColExpWork
open Formalism.REAL
namespace PI.QmColExpWork
theorem _root_.solution : PI.ExpFirstCol := fun _ _ _ _ _ E a b u => expFirst E a b u
end PI.QmColExpWork
