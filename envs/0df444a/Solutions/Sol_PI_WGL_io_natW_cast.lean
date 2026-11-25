-- Prove2me | solution 1 for PI.WGL.io_natW_cast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:09:10.829173+00:00
-- url     : https://prove2.me/submissions/8971ab71-39e6-4c17-89dd-8a6dbab6369d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_CapelliShift
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_IoExistsOfCap
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightIrreducible_BCRowGenMonomial
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_IoPolDiagHw

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGL
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
namespace PI.WGL
theorem _root_.solution {k : ℕ} (mu : DomWeight k) (a : Fin k) :
    ((mu.natW a : ℕ) : ℂ) = ((mu.w a - mu.detShift : ℤ) : ℂ) := by
  have hk : 0 < k := Fin.pos a
  have ha := a.isLt
  have hd : mu.detShift = mu.w ⟨k - 1, by omega⟩ := by
    unfold DomWeight.detShift
    rw [dif_pos hk]
  have hle : mu.w ⟨k - 1, by omega⟩ ≤ mu.w a := mu.anti (by
    rw [Fin.le_iff_val_le_val]
    show (a : ℕ) ≤ k - 1
    omega)
  have h0 : 0 ≤ mu.w a - mu.detShift := by omega
  show (((mu.w a - mu.detShift).toNat : ℕ) : ℂ) = _
  rw [← Int.cast_natCast, Int.toNat_of_nonneg h0]
end PI.WGL
