-- Prove2me | solution 1 for PI.WMI.lambda_integrality
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:10:39.317805+00:00
-- url     : https://prove2.me/submissions/7630676a-2250-4517-b6cd-37dc64040866

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_LowerInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_TorusEigenvalueFormula
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_WMI_lowerInv_torus_mem
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
theorem _root_.solution : LamInt := by
  intro N Λ H _ _ σ v hU hv hw a
  have hfun : (fun b => Complex.exp ((((Pi.single a (2 * Real.pi) : Fin N → ℝ) b : ℝ) : ℂ) * Complex.I))
      = fun _ => (1 : ℂ) := by
    funext b
    by_cases hb : b = a
    · subst hb
      simp only [Pi.single_eq_same]
      push_cast
      exact Complex.exp_two_pi_mul_I
    · simp [hb]
  have hmem := lowerInv_torus_mem (N := N) (Pi.single a (2 * Real.pi))
  have h := hw (Pi.single a (2 * Real.pi)) hmem
  rw [hfun, Matrix.diagonal_one, hU.1.1] at h
  have hsum : (∑ b, Λ b * (Pi.single a (2 * Real.pi) : Fin N → ℝ) b) = Λ a * (2 * Real.pi) := by
    simp [Pi.single_apply]
  rw [hsum] at h
  have he : Complex.exp (((Λ a * (2 * Real.pi) : ℝ) : ℂ) * Complex.I) = 1 := by
    by_contra hne
    apply hv
    have h2 : (1 - Complex.exp (((Λ a * (2 * Real.pi) : ℝ) : ℂ) * Complex.I)) • v = 0 := by
      rw [sub_smul, one_smul, ← h]
      simp
    exact (smul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr (Ne.symm hne))
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp he
  refine ⟨n, ?_⟩
  have hpi : (2 * (Real.pi : ℂ)) * Complex.I ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have : (Λ a : ℂ) = (n : ℂ) := by
    apply mul_right_cancel₀ hpi
    push_cast at hn
    linear_combination hn
  exact_mod_cast this
end PI.WMI
