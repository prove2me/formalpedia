-- Prove2me | solution 1 for PI.WMI.pe_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:10:48.652377+00:00
-- url     : https://prove2.me/submissions/ea1d9b46-25aa-409b-9bd6-68bf66ef01d9

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_IsPolyMon
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_PolyExtLem
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
theorem _root_.solution {N : ℕ} (h : Matrix (Fin N) (Fin N) ℂ) (Q : MvPolynomial (Fin N × Fin N) ℂ) :
    ∃ Q' : MvPolynomial (Fin N × Fin N) ℂ, ∀ g, evM g Q' = evM (g * h) Q := by
  refine ⟨bind₁ (fun pq : Fin N × Fin N => ∑ r, X (pq.1, r) * C (h r pq.2)) Q, fun g => ?_⟩
  induction Q using MvPolynomial.induction_on with
  | C a => simp [evM]
  | add p q hp hq => simp only [map_add, evM] at *; rw [hp, hq]
  | mul_X p n hp =>
    simp only [map_mul, evM, bind₁_X_right] at *
    rw [hp]
    simp [Matrix.mul_apply]
end PI.WMI
