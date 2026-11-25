-- Prove2me | solution 1 for P2M_PI_UnitaryGroupMassFormula_ScXuExists_target_of__fbce93cba525
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:54:27.150037+00:00
-- url     : https://prove2.me/submissions/2a73b968-e5cc-4ca9-9cf3-b0349608d796

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_LinDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_LocDefs
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_locCore_of
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_target_of


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
theorem _root_.solution (hI : LocIdem) (hS : LocSplitP) (hA : BridgeA) (hB : BridgeB) (hL : LocLin) (hG : Glue) :
    _root_.PI.ScXuExists.Target := by
  first
  | exact target_of hI (locCore_of hS hA hB hL) hG
  | exact target_of hI hG (locCore_of hS hA hB hL)
  | (unfold PI.ScXuExists.Target LocIdem Glue LocCore at *; done)
end PI.UnitaryGroupMassFormula.ScXuExists
