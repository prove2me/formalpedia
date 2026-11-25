-- Prove2me | solution 1 for PI.QnHermHaar.repTm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:08:47.276396+00:00
-- url     : https://prove2.me/submissions/69f40b16-e99b-4b74-9fad-18ffa853099b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_RepOnOfEq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_RepresentsTransferOneOne
import Theorems.Thm_PI_QnHermHaar_Gen_repOn_add
import Theorems.Thm_PI_QnHermHaar_Gen_repOn_algebraMap
import Theorems.Thm_PI_QnHermHaar_Gen_repOn_ite
import Theorems.Thm_PI_QnHermHaar_Gen_repOn_zero
import Theorems.Thm_PI_QnHermHaar_posL_inj
import Theorems.Thm_PI_QnHermHaar_repE
import Theorems.Thm_PI_QnHermHaar_repOn_of_eq


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
theorem _root_.solution (H : Hyp k r z z' i μ) (w : ℂ) (a b : Fin (mdim k r i)) :
    RepOn (hI H) (Tm (EA H) w a b) (Top (EH k r) w (posL k r i a) (posL k r i b)) := by
  have h := repOn_add (hI H) (repOn_ite (hI H) (a = b) (repOn_algebraMap (hI H) w) (repOn_zero (hI H)))
    (repE H a b)
  unfold Tm
  refine repOn_of_eq h fun f => ?_
  funext g
  by_cases hab : a = b
  · subst hab; simp [Formalism.QuantumDeterminants.Top, EOp]
  · have : posL k r i a ≠ posL k r i b := fun h => hab (posL_inj h)
    simp [Formalism.QuantumDeterminants.Top, EOp, hab, this]
end PI.QnHermHaar
