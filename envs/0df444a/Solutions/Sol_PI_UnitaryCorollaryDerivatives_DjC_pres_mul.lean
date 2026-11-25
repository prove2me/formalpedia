-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.DjC.pres_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:35:36.449239+00:00
-- url     : https://prove2.me/submissions/6d616763-b84e-4379-884e-a2a24512f61b

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
theorem _root_.solution {S : Set (Fin N)} {X Y : Matrix (Fin N) (Fin N) ℂ} (hX : Pres S X) (hY : Pres S Y) :
    Pres S (X * Y) := by
  intro c b hb hc
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun m _ => ?_
  by_cases hm : m ∈ S
  · rw [hX c m hm hc, zero_mul]
  · rw [hY m b hb hm, mul_zero]
end PI.UnitaryCorollaryDerivatives.DjC
