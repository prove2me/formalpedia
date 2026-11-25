-- Prove2me | solution 1 for PIW.HCFdeg.formal_degree_of_schur_unimodular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:49:04.470797+00:00
-- url     : https://prove2.me/submissions/96f21d6d-830a-4acb-8faa-2e2c6f8d08d0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_FormalDegreeOrthogonality
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_Partial
import Theorems.Thm_PIW_HCFdeg_formal_degree_orthogonality


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
open PI.UpqRep
namespace PIW.HCFdeg
theorem _root_.solution (hSchur : StSchur) (hBdd : StBdd) (hOrthOf : StOrthOf) (hUni : StUnimod) : StableSubspaceMobius :=
  formal_degree_orthogonality (hOrthOf hSchur hBdd) hUni
end PIW.HCFdeg
