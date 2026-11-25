-- Prove2me | solution 1 for PI.FJMX.minorProductDiagonal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:14:01.755713+00:00
-- url     : https://prove2.me/submissions/94d94d8e-dd5d-46d6-8592-df5a7aa27494

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurCauchy
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LeadTDerCols
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_CauBFin
import Theorems.Thm_PI_FJMX_shapeProd_diag
import Theorems.Thm_PI_FJMX_shapeProd_hwb


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.FJMX
namespace PI.FJMX
theorem _root_.solution : PI.FJMB.HypShape := fun _ _ ι hι α hα =>
  ⟨shapeProd_hwb ι hι _, shapeProd_diag ι hι α hα⟩
end PI.FJMX
