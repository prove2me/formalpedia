-- Prove2me | solution 1 for PI.RhsWLim.W.HU.amb_closed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:28:13.131404+00:00
-- url     : https://prove2.me/submissions/bf9d8b11-b951-47f1-b21a-dd70e0a62b59

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory Filter Topology Matrix
open scoped ENNReal
open PI PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.HU
open PI.RhsWLim
variable {k r : ℕ}
namespace PI.RhsWLim.W.HU
theorem _root_.solution : IsClosed (amb k r) := by
  show IsClosed {x : Mt k r | (Matrix.of x)ᴴ * Hpk k r * Matrix.of x = Hpk k r ∧
    ∀ a : Fin r, (Matrix.of x *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧
      Matrix.of x *ᵥ bvec (esI k r a) = bvec (esI k r a))}
  have hid : Continuous (fun x : Mt k r => (Matrix.of x : Mat k r)) := continuous_id
  rw [Set.ofPred_and, Set.ofPred_forall]
  refine IsClosed.inter (isClosed_eq ((hid.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul hid)
    continuous_const) (isClosed_iInter fun a => ?_)
  rw [Set.ofPred_and]
  exact (isClosed_eq (hid.matrix_mulVec continuous_const) continuous_const).inter
    (isClosed_eq (hid.matrix_mulVec continuous_const) continuous_const)
end PI.RhsWLim.W.HU
