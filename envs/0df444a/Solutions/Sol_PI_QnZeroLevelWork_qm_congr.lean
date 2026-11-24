-- Prove2me | solution 1 for PI.QnZeroLevelWork.qm_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:51:08.017136+00:00
-- url     : https://prove2.me/submissions/f3b770ea-f727-4e21-a8b5-782689a923c6

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroLevelIndex_SecondMinorZeroLevelFormula

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open PI PI.QnZeroLevelWork
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {k r : ℕ}
namespace PI.QnZeroLevelWork
theorem _root_.solution {n t : ℕ}
    (Eop : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E))
    (a a' b b' : Fin t → Fin n) (ha : a = a') (hb : b = b') (u : ℂ) (f : Matrix (Fin n) (Fin n) ℂ → E) :
    qminorOp Eop a b u f = qminorOp Eop a' b' u f := by
  subst ha hb
  rfl
end PI.QnZeroLevelWork
