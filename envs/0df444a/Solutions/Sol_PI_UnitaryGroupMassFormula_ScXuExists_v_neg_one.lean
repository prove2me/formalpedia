-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ScXuExists.v_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:43:25.765439+00:00
-- url     : https://prove2.me/submissions/01fdff39-5d1d-4215-a7d4-eaaf53083678

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_LinLeg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_LinMain

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
open Matrix
variable {K : Type} [Field K] (O : ValuationSubring K)
namespace PI.UnitaryGroupMassFormula.ScXuExists
theorem _root_.solution : O.valuation (-1 : K) = 1 := by
  first
  | simp
  | exact (Valuation.map_neg _ 1).trans (map_one _)
  | rw [Valuation.map_neg, map_one]
end PI.UnitaryGroupMassFormula.ScXuExists
