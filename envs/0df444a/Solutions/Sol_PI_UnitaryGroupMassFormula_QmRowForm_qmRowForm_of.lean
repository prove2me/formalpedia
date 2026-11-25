-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmRowForm.qmRowForm_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:50:41.000791+00:00
-- url     : https://prove2.me/submissions/0d9335c9-707a-4be3-a34d-ebcae07c6a2e

import Definitions.Def_Formalism_PeriodIntegrals_QmRowForm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RowFormPermutationSplit_Development
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmRowForm_rowForm_of

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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.QmRowForm
namespace PI.UnitaryGroupMassFormula.QmRowForm
theorem _root_.solution (h1 : DblDec) (h2 : DblInc) (h3 : DblPerm) : PI.QmRowForm := by
  unfold PI.QmRowForm
  exact rowForm_of h1 h2 h3
end PI.UnitaryGroupMassFormula.QmRowForm
