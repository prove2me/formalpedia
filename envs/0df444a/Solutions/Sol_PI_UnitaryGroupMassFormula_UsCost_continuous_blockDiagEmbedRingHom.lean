-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCost.continuous_blockDiagEmbedRingHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:49:05.112696+00:00
-- url     : https://prove2.me/submissions/e3dfc618-058f-40ff-8025-62891eeaaabe

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
theorem _root_.solution : Continuous (blockDiagEmbedRingHom k j ρ) := by
  show Continuous (fun x : B.Mat k ρ × Matrix (Fin j) (Fin j) ℂ => blk3 x.2 0 0 0 x.1 0 0 0 x.2)
  simp only [blk3]
  exact ((continuous_snd.matrix_fromBlocks continuous_const continuous_const continuous_fst).matrix_fromBlocks
    continuous_const continuous_const continuous_snd).matrix_reindex _ _
end PI.UnitaryGroupMassFormula.UsCost
