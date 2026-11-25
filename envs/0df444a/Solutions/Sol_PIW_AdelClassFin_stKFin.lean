-- Prove2me | solution 1 for PIW.AdelClassFin.stKFin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:02:07.184137+00:00
-- url     : https://prove2.me/submissions/dc8164e3-fc78-4f83-a371-1672e99b02a1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_IsImgTrans
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_KsetMulVecMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictAll
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_StHOfOpen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_Partial
import Theorems.Thm_PIW_AdelClassFin_lattice_dense
import Theorems.Thm_PIW_AdelClassFin_stKFin_of
import Theorems.Thm_PIW_AdelClassFin_stLatFin_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.AdelClassFin
namespace PIW.AdelClassFin
theorem _root_.solution : StKFin := stKFin_of (stLatFin_of lattice_dense)
end PIW.AdelClassFin
