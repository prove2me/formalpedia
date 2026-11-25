-- Prove2me | solution 1 for PI.StabPairsW.Fm_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:32:09.578089+00:00
-- url     : https://prove2.me/submissions/e32b32d8-effa-483f-9362-33746d1c717c

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
    (Fm k r z z' γ)ᴴ = Matrix.of fun i j => star (gramVec k r z z' γ i j) := by
  ext i j
  simp [Fm, Matrix.conjTranspose_apply]
end PI.StabPairsW
