-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCost.EB_hat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:52:12.015012+00:00
-- url     : https://prove2.me/submissions/e6930946-4c6d-4f20-a789-6520116aaed6

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_LetterSize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_Letters

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.Ux5
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCost
namespace PI.UnitaryGroupMassFormula.UsCost
theorem _root_.solution {k j ρ : ℕ} (Y : B.Mat k ρ) {c : ℝ} (hY : EB Y c) (hc : 0 ≤ c) :
    EB (blk3 (0 : Matrix (Fin j) (Fin j) ℂ) 0 0 0 Y 0 0 0 0 : B.Mat k (j + ρ)) c := by
  unfold EB blk3 at *
  intro a b
  show ‖fromBlocks (fromBlocks 0 0 0 Y) (fromRows 0 0) (fromCols 0 0) 0
    ((eB k j ρ).symm a) ((eB k j ρ).symm b)‖ ≤ c
  rcases (eB k j ρ).symm a with (a' | a') | a' <;> rcases (eB k j ρ).symm b with (b' | b') | b' <;>
    simp [hc, hY]
end PI.UnitaryGroupMassFormula.UsCost
