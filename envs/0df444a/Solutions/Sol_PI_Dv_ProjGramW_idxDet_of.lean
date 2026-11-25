-- Prove2me | solution 1 for PI.Dv.ProjGramW.idxDet_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:43:48.78924+00:00
-- url     : https://prove2.me/submissions/c3e70006-4e4a-4133-b28b-5ee27d0b257e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionGramMatrices_AlgebraMapNeZeroOfNotMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionGramMatrices_IdxDet
import Theorems.Thm_PI_Dv_ProjGramW_idx_reduce
import Theorems.Thm_PI_Dv_ProjGramW_idxStd_det

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.ProjGramW
open NumberField IsDedekindDomain Formalism.BasicNotions
namespace PI.Dv.ProjGramW
theorem _root_.solution (hI : IdxCalc) : IdxDet := by
  intro K _ _ V _ _ _ _ w d b hb C hC
  have := idx_reduce hI w hb C hC
  rw [idxStd_det hI w C hC] at this
  exact this
end PI.Dv.ProjGramW
