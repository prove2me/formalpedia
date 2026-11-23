-- Prove2me | solution 1 for PI.RL.W.theta_X
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:40:34.709855+00:00
-- url     : https://prove2.me/submissions/6a4b8651-8af0-4593-9c3f-b6531f5f958e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RowLetter
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RowDerivationChainRule_Development

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open PI PI.RL PI.RL.W
open PI.RL
namespace PI.RL.W
theorem _root_.solution (K : Type) [Field K] (m : ℕ) (vec : Bool) (c : Fin (m + 1)) :
    theta K m vec (X c) = Nv K m vec c := by
  simp [theta]
end PI.RL.W
