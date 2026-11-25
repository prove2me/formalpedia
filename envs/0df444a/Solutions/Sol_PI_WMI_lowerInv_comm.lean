-- Prove2me | solution 1 for PI.WMI.lowerInv_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:10:48.763801+00:00
-- url     : https://prove2.me/submissions/8abffdd1-1e0c-474e-bbcf-416de8e95f01

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
theorem _root_.solution {N : ℕ} {a b : Fin N} (hab : a < b) (θ : Fin N → ℝ) (c : ℂ) :
    (1 + Matrix.single b a c) * torus θ =
      torus θ * (1 + Matrix.single b a (c * lowerInv_e (θ a - θ b))) := by
  have key : Complex.exp ((θ b : ℂ) * Complex.I) * lowerInv_e (θ a - θ b) =
      Complex.exp ((θ a : ℂ) * Complex.I) := by
    unfold lowerInv_e
    rw [← Complex.exp_add]
    congr 1; push_cast; ring
  ext i j
  simp only [torus, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.single_apply]
  by_cases h : b = i ∧ a = j
  · obtain ⟨rfl, rfl⟩ := h
    simp only [and_self, if_true]
    rw [Matrix.one_apply_ne (ne_of_gt hab), ← key]; ring
  · simp only [if_neg h, add_zero]
    by_cases hij : i = j
    · subst hij; ring
    · rw [Matrix.one_apply_ne hij]; ring
end PI.WMI
