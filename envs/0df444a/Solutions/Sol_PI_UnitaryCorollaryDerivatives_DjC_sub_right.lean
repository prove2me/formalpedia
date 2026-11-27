-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.DjC.sub_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:18:06.679529+00:00
-- url     : https://prove2.me/submissions/da8f9ad0-e3e1-4215-afa0-e8dce249af7f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CoreStar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SumEqSumCompEmbedding
import Definitions.Def_Lemmata_B110_ExistsMoved
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_DjCurveA
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_DjC_sum_emb

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
theorem _root_.solution (e : Fin j ↪ Fin N) (row : Fin j → Fin N) (h E : Matrix (Fin N) (Fin N) ℂ)
    (hE : Pres (Set.range e) E) :
    (Matrix.of fun a b => (h * E) (row a) (e b)) = (Matrix.of fun a b => h (row a) (e b)) * sub e E := by
  ext a b
  rw [Matrix.of_apply, Matrix.mul_apply, Matrix.mul_apply]
  exact sum_emb e _ fun c hc => by rw [hE c (e b) ⟨b, rfl⟩ hc, mul_zero]
end PI.UnitaryCorollaryDerivatives.DjC
