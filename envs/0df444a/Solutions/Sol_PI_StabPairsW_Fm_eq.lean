-- Prove2me | solution 1 for PI.StabPairsW.Fm_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:49:46.81807+00:00
-- url     : https://prove2.me/submissions/067ac8e6-16d5-499b-9f84-a944ac18601b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_ConverseStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_IsUnitDetOfMemGV

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
open PI PI.StabPairsW
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
variable {k r : ℕ}
namespace PI.StabPairsW
theorem _root_.solution (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) :
    Fm k r z z' γ = Matrix.fromCols (Ff k r z) (γ * Ff k r z') := by
  ext i j
  cases j <;> simp [Fm, Ff, gramVec, Matrix.mulVec, dotProduct, Matrix.mul_apply]
end PI.StabPairsW
