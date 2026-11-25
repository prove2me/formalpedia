-- Prove2me | solution 1 for PI.ET.expTri_of_horn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:49:17.191975+00:00
-- url     : https://prove2.me/submissions/26caa1d7-87d0-443e-a974-99f9de80a453

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialTriangular_ExpTriOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialTriangular_SpecExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialTriangular_PsumEqRange
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialTriangular_ExpTriOfHorn
import Theorems.Thm_PI_ET_abelSq
import Theorems.Thm_PI_ET_euclTri
import Theorems.Thm_PI_ET_expTri_of
import Theorems.Thm_PI_ET_hsEq
import Theorems.Thm_PI_ET_specExists


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.ET
namespace PI.ET
theorem _root_.solution (hH : Horn) : PI.ExpTri :=
  expTri_of specExists hsEq hH abelSq euclTri
end PI.ET
