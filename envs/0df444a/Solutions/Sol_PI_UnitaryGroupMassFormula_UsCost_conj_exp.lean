-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCost.conj_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:49:01.299814+00:00
-- url     : https://prove2.me/submissions/a904ad23-a6fb-49ac-8406-13d096ad9c73

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_LetterSize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_ContinuousBlockDiagEmbedRingHom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCost
variable {k j ρ : ℕ}
namespace PI.UnitaryGroupMassFormula.UsCost
theorem _root_.solution {m : ℕ} (n X : Matrix (Fin m) (Fin m) ℂ) (hn : n * n⁻¹ = 1) :
    n⁻¹ * NormedSpace.exp X * n = NormedSpace.exp (n⁻¹ * X * n) :=
  (Matrix.exp_conj' n X ((Matrix.isUnit_iff_isUnit_det n).2 (Matrix.isUnit_det_of_right_inverse hn))).symm
end PI.UnitaryGroupMassFormula.UsCost
