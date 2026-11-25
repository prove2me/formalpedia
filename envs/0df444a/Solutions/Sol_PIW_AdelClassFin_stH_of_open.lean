-- Prove2me | solution 1 for PIW.AdelClassFin.stH_of_open
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:17:29.651805+00:00
-- url     : https://prove2.me/submissions/024412eb-d5cd-436b-9745-b3bccd1f3dcc

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_HformSelfStar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_HmkFactor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_UnitsModSq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_PartShortOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_PartSplitOfOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_HformSmulRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_StHOfOpen
import Theorems.Thm_PIW_AdelClassFin_partIso_of
import Theorems.Thm_PIW_AdelClassFin_partMink
import Theorems.Thm_PIW_AdelClassFin_partShort_of
import Theorems.Thm_PIW_AdelClassFin_partSplit_of_one
import Theorems.Thm_PIW_AdelClassFin_partUnits
import Theorems.Thm_PIW_AdelClassFin_stH_of_parts


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PIW PIW.AdelClassFin
namespace PIW.AdelClassFin
theorem _root_.solution (hO : SpOne) (hI : IdealBoundAll) (h1 : SvMajE) (h2 : SvCodiff) (h3 : SvBasis) (h4 : SvGramDet)
    (h5 : SvReal) : StH :=
  stH_of_parts (partShort_of partMink h1 h2 h3 h4 h5) partUnits (partIso_of hI) (partSplit_of_one hO)
end PIW.AdelClassFin
