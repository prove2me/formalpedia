-- Prove2me | solution 1 for PI.WSF.ci_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:12:24.120967+00:00
-- url     : https://prove2.me/submissions/036bc030-9caf-46fa-b8e9-dda5fbc8c3b6

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


section
noncomputable section
namespace PI.WSF
open MvPolynomial MeasureTheory Matrix
private theorem evalM_rowAct {N : ℕ} (u x : Matrix (Fin N) (Fin N) ℂ)
    (p : MvPolynomial (Fin N × Fin N) ℂ) :
    evalM x (Formalism.GradedWeylDivisibility.rowAct ℂ u p) = evalM (u * x) p := by
  induction p using MvPolynomial.induction_on
  next a =>
    simp [evalM, Formalism.GradedWeylDivisibility.rowAct]
  next p q hp hq =>
    rw [map_add, ci_evalM_add, ci_evalM_add, hp, hq]
  next p v hp =>
    simp only [evalM, map_mul] at hp ⊢
    rw [hp]
    congr 1
    simp [Formalism.GradedWeylDivisibility.rowAct, Matrix.mul_apply]
end PI.WSF
end
end

set_option autoImplicit false
noncomputable section
open PI PI.WSF
open MvPolynomial MeasureTheory Matrix
namespace PI.WSF
theorem _root_.solution {N : ℕ} {μ : Measure (Matrix (Fin N) (Fin N) ℂ)} (hμ : IsHaarU N μ)
    (u : Matrix (Fin N) (Fin N) ℂ) (hu : u ∈ unitaryGroup (Fin N) ℂ) (p q : MvPolynomial (Fin N × Fin N) ℂ) :
    Aform μ (Formalism.GradedWeylDivisibility.rowAct ℂ u p) (Formalism.GradedWeylDivisibility.rowAct ℂ u q) = Aform μ p q := by
  obtain ⟨-, -, -, hL⟩ := hμ
  unfold Aform
  simp only [evalM_rowAct]
  exact hL u hu (fun x => evalM x p * star (evalM x q)) (ci_cont2 p q)
end PI.WSF
