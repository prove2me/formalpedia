-- Prove2me | solution 1 for PI.QnRT.e_ne_es
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:48:50.91+00:00
-- url     : https://prove2.me/submissions/7bbb6b3a-eb33-4396-a017-b9b6549c8e6f

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusConjugationRule_WColOther

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
open PI PI.QnRT
variable {k r : ℕ}
namespace PI.QnRT
theorem _root_.solution (l : Fin r) : eI k r l ≠ esI k r l := by
  intro h
  have hl := l.isLt
  have h' := congrArg Fin.val h
  simp only [eI, esI] at h'
  omega
end PI.QnRT
