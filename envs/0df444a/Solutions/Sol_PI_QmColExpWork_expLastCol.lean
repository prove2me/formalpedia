-- Prove2me | solution 1 for PI.QmColExpWork.expLastCol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:13:16.123063+00:00
-- url     : https://prove2.me/submissions/e9cc0e06-c696-4b9e-a79d-5ad15fbb6b63

import Definitions.Def_Formalism_PeriodIntegrals_QmColExp
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialFirstColumn_FirstColumnSplitBijective
import Theorems.Thm_PI_QmColExpWork_expLast

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
theorem _root_.solution : PI.ExpLastCol := fun _ _ _ _ _ E a b u => expLast E a b u
end PI.QmColExpWork
