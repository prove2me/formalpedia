-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.DjC.pres_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:58:25.260265+00:00
-- url     : https://prove2.me/submissions/a2c38713-8f39-4d48-b944-7f3723fdb71b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CoreStar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SumEqSumCompEmbedding
import Definitions.Def_Lemmata_B110_ExistsMoved
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_DjCurveA
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_DjC_pres_mul

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
theorem _root_.solution {S : Set (Fin N)} {Y : Matrix (Fin N) (Fin N) ℂ} (hY : Pres S Y) (n : ℕ) :
    Pres S (Y ^ n) := by
  induction n with
  | zero =>
    intro c b hb hc
    rw [pow_zero, Matrix.one_apply_ne]
    rintro rfl; exact hc hb
  | succ n ih => rw [pow_succ]; exact pres_mul ih hY
end PI.UnitaryCorollaryDerivatives.DjC
