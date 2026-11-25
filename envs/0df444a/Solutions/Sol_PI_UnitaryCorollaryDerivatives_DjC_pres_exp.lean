-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.DjC.pres_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:12:20.071492+00:00
-- url     : https://prove2.me/submissions/57cb04da-0490-4828-84c8-76e2755ea5a1

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CoreStar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SumEqSumCompEmbedding
import Definitions.Def_Lemmata_B110_ExistsMoved
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_DjCurveA
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_DjC_pres_pow

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
open scoped Matrix.Norms.Operator
namespace PI.UnitaryCorollaryDerivatives.DjC
theorem _root_.solution {S : Set (Fin N)} {Y : Matrix (Fin N) (Fin N) ℂ} (hY : Pres S Y) :
    Pres S (NormedSpace.exp Y) := by
  intro c b hb hc
  have h := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) Y
  have h1 := Pi.hasSum.1 h c
  have h2 := Pi.hasSum.1 h1 b
  have h3 : HasSum (fun n : ℕ => ((n.factorial : ℂ)⁻¹ • Y ^ n) c b) 0 := by
    have : (fun n : ℕ => ((n.factorial : ℂ)⁻¹ • Y ^ n) c b) = fun _ => 0 := by
      funext n; rw [Matrix.smul_apply, pres_pow hY n c b hb hc, smul_zero]
    rw [this]; exact hasSum_zero
  exact h2.unique h3
end PI.UnitaryCorollaryDerivatives.DjC
