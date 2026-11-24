-- Prove2me | solution 1 for PIW.AdelClassFin.dictTop_fmat_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:33:33.379527+00:00
-- url     : https://prove2.me/submissions/bf82d0c3-0753-4469-963d-b25adb79752f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictPlan
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Bridge
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_RationalPointsLeHolds
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsDual
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictTop

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
theorem _root_.solution (I : AutInst) (x y : I.Gf) : I.fmat (x * y) = I.fmat x * I.fmat y := rfl
end PIW.AdelClassFin
