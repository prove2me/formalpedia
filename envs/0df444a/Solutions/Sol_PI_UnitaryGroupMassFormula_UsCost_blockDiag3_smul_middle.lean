-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCost.blockDiag3_smul_middle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:57:50.28971+00:00
-- url     : https://prove2.me/submissions/8652824c-fc0f-451a-a8fa-9fa4dcc9544a

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
theorem _root_.solution (c : ℂ) (Y : B.Mat k ρ) :
    (blk3 0 0 0 0 (c • Y) 0 0 0 0 : B.Mat k (j + ρ)) = c • blk3 0 0 0 0 Y 0 0 0 0 := by
  ext a b
  simp only [blk3, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.smul_apply]
  generalize (eB k j ρ).symm a = x
  generalize (eB k j ρ).symm b = y
  rcases x with (x | x) | x <;> rcases y with (y | y) | y <;> simp
end PI.UnitaryGroupMassFormula.UsCost
