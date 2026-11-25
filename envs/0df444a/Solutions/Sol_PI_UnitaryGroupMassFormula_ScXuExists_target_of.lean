-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ScXuExists.target_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:33:32.094391+00:00
-- url     : https://prove2.me/submissions/b9d79ebf-3ab8-4f85-8bcd-58fa865c2948

import Definitions.Def_Formalism_PeriodIntegrals_ScXuExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_Commensurated
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_MemLocFrom
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_Development
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_locXu_of

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
theorem _root_.solution (hI : LocIdem) (hC : LocCore) (hG : Glue) : _root_.PI.ScXuExists.Target :=
  hG (locXu_of hI hC)
end PI.UnitaryGroupMassFormula.ScXuExists
