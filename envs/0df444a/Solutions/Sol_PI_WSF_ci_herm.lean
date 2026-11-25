-- Prove2me | solution 1 for PI.WSF.ci_herm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:12:22.166167+00:00
-- url     : https://prove2.me/submissions/2ac14151-17a0-4ba4-9881-1ffcba855f4f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SchurOrthogonality_CrRowActRowAct
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SchurOrthogonality_CiEvalMSmul
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.WSF
open MvPolynomial MeasureTheory Matrix
namespace PI.WSF
theorem _root_.solution {N : ℕ} (μ : Measure (Matrix (Fin N) (Fin N) ℂ)) (p q : MvPolynomial (Fin N × Fin N) ℂ) :
    Aform μ q p = star (Aform μ p q) := by
  unfold Aform
  have h := integral_conj (μ := μ) (f := fun x => evalM x p * star (evalM x q))
  rw [show star (∫ x, evalM x p * star (evalM x q) ∂μ) =
    (starRingEnd ℂ) (∫ x, evalM x p * star (evalM x q) ∂μ) from rfl, ← h]
  congr 1
  funext x
  simp [mul_comm]
end PI.WSF
