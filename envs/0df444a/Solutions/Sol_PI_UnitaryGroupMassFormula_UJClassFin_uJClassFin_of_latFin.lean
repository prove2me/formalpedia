-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassFin.uJClassFin_of_latFin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:25:30.280851+00:00
-- url     : https://prove2.me/submissions/7190b774-51b6-4c14-b40f-a28c342d5dcb

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_UJClassFinOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_RationalPointsDense
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_ClassFiniteOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_UJClassFinOfLatFin
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_classFinite_of
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_rational_points_dense
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_uJClassFin_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassFin
namespace PI.UnitaryGroupMassFormula.UJClassFin
theorem _root_.solution (hS : SigPos) (hA : AdelBounds) (hB : LatFin) : PI.UJClassFin.UJClassFin :=
  uJClassFin_of rational_points_dense (classFinite_of hS hA hB)
end PI.UnitaryGroupMassFormula.UJClassFin
