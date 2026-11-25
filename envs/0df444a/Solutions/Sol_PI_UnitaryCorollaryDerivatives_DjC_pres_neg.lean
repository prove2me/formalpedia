-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.DjC.pres_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:35:39.569138+00:00
-- url     : https://prove2.me/submissions/a8e518d4-8ad0-48b5-ba19-8d867d545337

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CoreStar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SumEqSumCompEmbedding
import Definitions.Def_Lemmata_B110_ExistsMoved
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_DjCurveA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.UnitaryCorollaryDerivatives PI.UnitaryCorollaryDerivatives.DjC
variable {N j : ℕ}
namespace PI.UnitaryCorollaryDerivatives.DjC
theorem _root_.solution {S : Set (Fin N)} {Y : Matrix (Fin N) (Fin N) ℂ} (hY : Pres S Y) : Pres S (-Y) := by
  intro c b hb hc
  rw [Matrix.neg_apply, hY c b hb hc, neg_zero]
end PI.UnitaryCorollaryDerivatives.DjC
