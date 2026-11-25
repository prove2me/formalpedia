-- Prove2me | solution 1 for PI.WMI.lowerInv_evM_affine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:10:12.902924+00:00
-- url     : https://prove2.me/submissions/4d771286-b5a3-4441-babc-5db8142b4aa3

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_IsPolyMon
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_LowerInv
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
open PI PI.WMI
open PI.UpqRep Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial Matrix
open scoped InnerProductSpace
namespace PI.WMI
theorem _root_.solution {N : ℕ} (A B : Matrix (Fin N) (Fin N) ℂ)
    (Q : MvPolynomial (Fin N × Fin N) ℂ) :
    ∃ p : Polynomial ℂ, ∀ c : ℂ, evM (A + c • B) Q = p.eval c := by
  induction Q using MvPolynomial.induction_on with
  | C r => exact ⟨Polynomial.C r, fun c => by simp [evM]⟩
  | add p q hp hq =>
    obtain ⟨p1, h1⟩ := hp
    obtain ⟨q1, h2⟩ := hq
    refine ⟨p1 + q1, fun c => ?_⟩
    have e : evM (A + c • B) (p + q) = evM (A + c • B) p + evM (A + c • B) q := by
      simp [evM]
    rw [e, h1, h2, Polynomial.eval_add]
  | mul_X p i hp =>
    obtain ⟨p1, h1⟩ := hp
    refine ⟨p1 * (Polynomial.C (A i.1 i.2) + Polynomial.C (B i.1 i.2) * Polynomial.X), fun c => ?_⟩
    have e : evM (A + c • B) (p * X i) = evM (A + c • B) p * (A i.1 i.2 + c * B i.1 i.2) := by
      simp [evM]
    rw [e, h1, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_C, Polynomial.eval_X]
    ring
end PI.WMI
