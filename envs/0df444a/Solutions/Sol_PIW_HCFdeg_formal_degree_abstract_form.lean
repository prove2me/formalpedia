-- Prove2me | solution 1 for PIW.HCFdeg.formal_degree_abstract_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:15:48.261081+00:00
-- url     : https://prove2.me/submissions/f0f324bd-136c-48b2-ab47-7305ee8d0067

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_Partial
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_CommuteStar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_ContinuousToL2Map
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_IntegrableCf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_Unimod
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_Closed
import Theorems.Thm_PIW_HCFdeg_formal_degree_of_schur_unimodular
import Theorems.Thm_PIW_HCFdeg_stBdd
import Theorems.Thm_PIW_HCFdeg_stOrthOf
import Theorems.Thm_PIW_HCFdeg_stSchur
import Theorems.Thm_PIW_HCFdeg_stUnimod


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.HCFdeg
namespace PIW.HCFdeg
theorem _root_.solution : StableSubspaceMobius := formal_degree_of_schur_unimodular stSchur stBdd stOrthOf stUnimod
end PIW.HCFdeg
