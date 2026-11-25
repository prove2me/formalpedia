-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ScXuExists.locXu_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:13:43.846041+00:00
-- url     : https://prove2.me/submissions/4c9e4597-6be6-4881-96ab-a307cf4629c6

import Definitions.Def_Formalism_PeriodIntegrals_ScXuExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_Commensurated
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_MemLocFrom
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_Development

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ScXuExists
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S PI.ScRefExists
namespace PI.UnitaryGroupMassFormula.ScXuExists
theorem _root_.solution (hI : LocIdem) (hC : LocCore) : LocXu := by
  intro I g r k e f z Rf hH v hv
  exact hC I g r k e f z Rf hH v hv (hI I g r k e f Rf hH.1 hH.2.2.1 v hv)
end PI.UnitaryGroupMassFormula.ScXuExists
