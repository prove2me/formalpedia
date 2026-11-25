-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCost.embG_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:04:50.389943+00:00
-- url     : https://prove2.me/submissions/b9c855f6-dde9-4469-a639-09935b79140c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_LetterSize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_ContinuousBlockDiagEmbedRingHom
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_continuous_blockDiagEmbedRingHom
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_exp_pair

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
    embG k j ρ (NormedSpace.exp Y) = NormedSpace.exp (blk3 0 0 0 0 Y 0 0 0 0 : B.Mat k (j + ρ)) := by
  have h := (open scoped Norms.Operator in
    NormedSpace.map_exp (blockDiagEmbedRingHom k j ρ) continuous_blockDiagEmbedRingHom ((Y, 0) : B.Mat k ρ × Matrix (Fin j) (Fin j) ℂ))
  exact (congrArg (blockDiagEmbedRingHom k j ρ) (exp_pair (j := j) Y)).symm.trans h
end PI.UnitaryGroupMassFormula.UsCost
