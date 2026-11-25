-- Prove2me | solution 1 for PI.RL.W.Nv_false_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:12:47.829017+00:00
-- url     : https://prove2.me/submissions/87972e3b-3204-4210-ba6b-740f76a6918f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RowDerivationChainRule_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RowDerivationChainRule_DetDer
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RowDerivationChainRule_NvFalseEq

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
theorem _root_.solution (K : Type) [Field K] (m : ℕ) (c : Fin (m + 1)) :
    Nv K m false c = ((genM K m).updateRow c (Pi.single (Fin.last m) 1)).det := by
  simp [Nv, Matrix.adjugate_apply]
end PI.RL.W
