-- Prove2me | solution 1 for PIW.AdelClassFin.stKFin_of_dense
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:18:48.289793+00:00
-- url     : https://prove2.me/submissions/eeff255b-ed41-4239-a753-64b6bf899c71

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_StGenusOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictPlan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_KsetMulVecMem
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
open Formalism.MainNotions.S PI.AdelClassFin NumberField
open scoped TensorProduct Matrix
namespace PIW.AdelClassFin
theorem _root_.solution (h : LDense) : StKFin := stKFin_of (stLatFin_of h)
end PIW.AdelClassFin
