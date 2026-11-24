-- Prove2me | solution 1 for PI.FrameInd.UPosW.cols_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:42:24.107177+00:00
-- url     : https://prove2.me/submissions/206945de-dd69-42ef-897a-ab609c48dbb5

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameInduction_NegBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameInduction_ColsConjTranspose

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
noncomputable section
open PI PI.FrameInd PI.FrameInd.UPosW
namespace PI.FrameInd.UPosW
theorem _root_.solution (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) :
    (cols k r z z' γ)ᴴ = Matrix.of fun i j => star (gramVec k r z z' γ i j) := by
  ext i j
  simp only [cols, Matrix.conjTranspose_apply, Matrix.of_apply]
end PI.FrameInd.UPosW
