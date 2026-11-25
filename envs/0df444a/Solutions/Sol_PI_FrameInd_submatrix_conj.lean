-- Prove2me | solution 1 for PI.FrameInd.submatrix_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:47:35.45239+00:00
-- url     : https://prove2.me/submissions/aaf0d8fb-cb1c-44ff-9beb-347334ca9a9b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameInduction_Counts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameInduction_NegativeBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameInduction_QBuild

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
theorem _root_.solution {ι κ : Type*} [Fintype ι] [Fintype κ] (W M : Matrix ι ι ℂ) (e : κ ≃ ι) :
    (W.submatrix id e)ᴴ * M * W.submatrix id e = (Wᴴ * M * W).submatrix e e := by
  ext i j
  simp [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.conjTranspose_apply]
end PI.FrameInd
