-- Prove2me | solution 1 for PI.BesselDerivW.exp_contDiff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:39:47.547006+00:00
-- url     : https://prove2.me/submissions/095bb990-66db-4136-892e-f6e9d6f58124

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BesselDerivatives_ContDiffOnDirectionalDerivative
import Definitions.Def_Formalism_PeriodIntegrals_BesselDeriv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BesselDerivatives_ExpSup
import Theorems.Thm_PI_BesselDerivW_exp_entry_contDiff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff Topology
open Matrix
noncomputable section
open PI PI.BesselDerivW
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PI.BesselDerivW
theorem _root_.solution (X : Matrix (Fin n) (Fin n) ℂ) :
    ContDiff ℝ ∞ (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  exact exp_entry_contDiff X i j
end PI.BesselDerivW
