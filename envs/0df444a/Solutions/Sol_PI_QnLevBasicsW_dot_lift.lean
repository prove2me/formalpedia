-- Prove2me | solution 1 for PI.QnLevBasicsW.dot_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:57:55.253047+00:00
-- url     : https://prove2.me/submissions/821a2f84-3f6c-435c-805d-69c85a4aa0ae

import Definitions.Def_Formalism_FormalDegreeBessel_StatementRP
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelLiftBasics_SplitInvInjective
import Theorems.Thm_PI_QnLevBasicsW_liftVec_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.QnLevBasicsW
open Formalism.QuantumDeterminants
variable {k i r' : ℕ}
namespace PI.QnLevBasicsW
theorem _root_.solution (v w : Fin (2 * r' + k + 1) → ℂ) :
    star (liftVec k i r' w) ⬝ᵥ liftVec k i r' v = star w ⬝ᵥ v := by
  rw [liftVec_eq, liftVec_eq]
  simp only [dotProduct, Pi.star_apply, Function.comp_apply]
  rw [Fintype.sum_equiv (split k i r') _ (fun s => star (Sum.elim w 0 s) * Sum.elim v 0 s) (fun _ => rfl)]
  simp [Fintype.sum_sum_type]
end PI.QnLevBasicsW
