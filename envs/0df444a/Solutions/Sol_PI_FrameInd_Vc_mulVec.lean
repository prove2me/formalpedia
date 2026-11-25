-- Prove2me | solution 1 for PI.FrameInd.Vc_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:40:47.993475+00:00
-- url     : https://prove2.me/submissions/857d6897-ce01-46ad-920e-601987fd0ac3

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameInduction_NegBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameInduction_FinrankUperpOfDet

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
open PI PI.FrameInd
namespace PI.FrameInd
theorem _root_.solution (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) (c : Fin (r + 1) ⊕ Fin (r + 1) → ℂ) :
    Vc k r z z' g *ᵥ c = ∑ i, c i • gramVec k r z z' g i := by
  ext l
  simp [Vc, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
end PI.FrameInd
