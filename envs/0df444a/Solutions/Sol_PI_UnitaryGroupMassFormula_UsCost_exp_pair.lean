-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCost.exp_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:48:42.928214+00:00
-- url     : https://prove2.me/submissions/42c8b7d1-765a-44ce-97ba-b21d5e519a1b

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
theorem _root_.solution (Y : B.Mat k ρ) :
    NormedSpace.exp ((Y, 0) : B.Mat k ρ × Matrix (Fin j) (Fin j) ℂ) = (NormedSpace.exp Y, 1) := by
  open scoped Norms.Operator in
  ext1
  · exact Prod.fst_exp _
  · exact (Prod.snd_exp _).trans NormedSpace.exp_zero
end PI.UnitaryGroupMassFormula.UsCost
