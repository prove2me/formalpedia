-- Prove2me | solution 1 for PI.QnHermHaar.repQminor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:18:20.069501+00:00
-- url     : https://prove2.me/submissions/3f6236b3-1574-4019-a007-91bc02092293

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_RepOnOfEq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_RepresentsTransferOneOne
import Theorems.Thm_PI_QnHermHaar_repTm
import Theorems.Thm_PI_QnHermHaar_Gen_repOn_intCast
import Theorems.Thm_PI_QnHermHaar_Gen_repOn_list
import Theorems.Thm_PI_QnHermHaar_Gen_repOn_mul
import Theorems.Thm_PI_QnHermHaar_Gen_repOn_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset MeasureTheory
open scoped ContDiff
noncomputable section
open PI PI.QnHermHaar
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Gen
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {i : Fin (r + 1)} {μ : Measure (Mt k r)}
namespace PI.QnHermHaar
theorem _root_.solution (H : Hyp k r z z' i μ) {t : ℕ} (a b : Fin t → Fin (mdim k r i)) (w : ℂ) :
    RepOn (hI H) (qminor (EA H) a b w) (qminorOp (EH k r) (posL k r i ∘ a) (posL k r i ∘ b) w) := by
  unfold qminor
  exact repOn_sum (hI H) Finset.univ fun σ _ => repOn_mul (hI H) (repOn_intCast (hI H) _)
    (repOn_list (hI H) t _ _ fun k' => repTm H _ _ _)
end PI.QnHermHaar
