-- Prove2me | solution 1 for PI.QnRT.exp_diag2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:11:10.009877+00:00
-- url     : https://prove2.me/submissions/960f7107-6193-4f88-9944-82f58881cf39

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
theorem _root_.solution (l : Fin r) (x y : ℂ) :
    NormedSpace.exp (diagonal (fun p => if p = eI k r l then x else if p = esI k r l then y else 0) : Mx k r) =
      dg l (Complex.exp x) (Complex.exp y) := by
  rw [Matrix.exp_diagonal]
  unfold dg
  congr 1
  funext p
  first
    | rw [Pi.exp_apply]
    | rw [NormedSpace.Pi.exp_apply]
    | rw [NormedSpace.exp_apply]
    | simp only [Pi.exp_def]
  split_ifs <;> simp [Complex.exp_eq_exp_ℂ]
end PI.QnRT
