-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ScXuExists.locCore_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:03:56.628557+00:00
-- url     : https://prove2.me/submissions/4bc9ccf8-4769-4c2a-880d-830adcedcf55

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_LinDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_LocDefs
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_linConcl_of

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
theorem _root_.solution (hS : LocSplitP) (hA : BridgeA) (hB : BridgeB) (hL : LocLin) : LocCore := by
  intro I g r k e f z Rf hH v hv hsum
  obtain ⟨p1, hp1⟩ := hS I g r k e f Rf v hsum
  obtain ⟨t, ht1, ht2⟩ := hH.2.2.2.2.2.2.2.1
  obtain ⟨T, hT⟩ := linConcl_of hL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (hA I g r k e f z Rf hH v hv hsum p1 hp1 t ht1 ht2)
  exact hB I g r k e f z Rf hH v hv hsum p1 hp1 T hT
end PI.UnitaryGroupMassFormula.ScXuExists
