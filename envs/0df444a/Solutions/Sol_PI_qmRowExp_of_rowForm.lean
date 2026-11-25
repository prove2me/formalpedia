-- Prove2me | solution 1 for PI.qmRowExp_of_rowForm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:17:47.237999+00:00
-- url     : https://prove2.me/submissions/9df2a98e-ac5d-4ef8-8b01-6dc3e788edd0

import Definitions.Def_Formalism_PeriodIntegrals_QmRowExp
import Definitions.Def_Formalism_PeriodIntegrals_QmRowForm
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RowExpansionMinor_FirstColumnSplitBijective
import Theorems.Thm_PI_QmRowExpWork_expFirstRow_of
import Theorems.Thm_PI_QmRowExpWork_expLastRow_of

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
open PI
namespace PI
theorem _root_.solution (h : PI.QmRowForm) : PI.QmRowExp :=
  ⟨QmRowExpWork.expFirstRow_of h, QmRowExpWork.expLastRow_of h⟩
end PI
