-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.DjC.sub_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:18:02.5898+00:00
-- url     : https://prove2.me/submissions/c324b3f3-aba3-4816-88ff-7fa998308d25

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
theorem _root_.solution (e : Fin j ↪ Fin N) (col : Fin j → Fin N) (h E : Matrix (Fin N) (Fin N) ℂ)
    (hE : Pres (Set.range e)ᶜ E) :
    (Matrix.of fun a b => (E * h) (e a) (col b)) = sub e E * (Matrix.of fun a b => h (e a) (col b)) := by
  ext a b
  rw [Matrix.of_apply, Matrix.mul_apply, Matrix.mul_apply]
  exact sum_emb e _ fun c hc => by rw [hE (e a) c hc (fun h' => h' ⟨a, rfl⟩), zero_mul]
end PI.UnitaryCorollaryDerivatives.DjC
