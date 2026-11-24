-- Prove2me | solution 1 for PI.FrameInd.herm_mulVec_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:42:25.917914+00:00
-- url     : https://prove2.me/submissions/dde070a7-953a-4030-b049-e1b96ba1b8e2

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
theorem _root_.solution {ι κ : Type*} [Fintype ι] [Fintype κ] (H : Matrix ι ι ℂ) (A : Matrix ι κ ℂ)
    (v w : κ → ℂ) : herm H (A *ᵥ v) (A *ᵥ w) = herm (Aᴴ * H * A) v w := by
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
end PI.FrameInd
