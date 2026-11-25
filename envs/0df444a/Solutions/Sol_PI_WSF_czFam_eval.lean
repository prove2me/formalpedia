-- Prove2me | solution 1 for PI.WSF.czFam_eval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:12:10.033899+00:00
-- url     : https://prove2.me/submissions/1dae7f1b-2c15-479f-b3ee-ceb3304f5057

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SchurOrthogonality_InstMeasurableSpaceMat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SchurOrthogonality_CzDiagUnitary
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.WSF
open MvPolynomial Matrix
open scoped ComplexOrder
namespace PI.WSF
theorem _root_.solution {N : ℕ} (u v : Matrix (Fin N) (Fin N) ℂ) (P : MvPolynomial (Fin N × Fin N) ℂ)
    (z : Fin N → ℂ) : eval z (czFam u v P) = evalM (u * diagonal z * v) P := by
  have h1 : eval z (czFam u v P) =
      eval (fun w : Fin N × Fin N => eval z (∑ c : Fin N, C (u w.1 c * v c w.2) * X c)) P := by
    unfold czFam
    exact MvPolynomial.eval₂Hom_bind₁ _ _ _ _
  rw [h1]
  unfold evalM
  refine congrArg (fun x => eval x P) ?_
  funext w
  simp only [map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring
end PI.WSF
