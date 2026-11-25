-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.im_pi_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:04:46.52588+00:00
-- url     : https://prove2.me/submissions/82283a2d-29d2-4098-b430-c24a21e17c6a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepSingleSat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_DescentStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_HNsmulNsmul
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_rep_kappa_eq
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_smulHom_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PI.UnitaryGroupMassFormula.UnimodLocStd.smulHom_apply



set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS
variable (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0)
  (m : Type) [Fintype m] [DecidableEq m]
variable {a b c d ha hd lam hlam m}
namespace PI.UnitaryGroupMassFormula.UnimodLocStd
theorem _root_.solution (n c₂ : ℤ) :
    ((2 * cmTheta b d - b)⁻¹ * (repKappa a b d ha hd lam hlam * ((n : ℂ) - c₂ * conj (cmTheta b d)))).im =
      -((2 * n - c₂ * b : ℤ) : ℝ) / d := by
  rw [rep_kappa_eq]
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hs : Real.sqrt d ≠ 0 := (Real.sqrt_pos.2 hd').ne'
  have hsq : Real.sqrt d * Real.sqrt d = d := Real.mul_self_sqrt hd'.le
  have hpi : 2 * cmTheta b d - b = Complex.I * ((Real.sqrt d : ℝ) : ℂ) := by
    unfold cmTheta
    ring
  have hconj : conj (cmTheta b d) = ((b : ℂ) - Complex.I * ((Real.sqrt d : ℝ) : ℂ)) / 2 := by
    unfold cmTheta
    simp [map_div₀, Complex.conj_ofReal, map_ofNat]
    ring
  rw [hpi, hconj]
  simp [Complex.mul_im, Complex.mul_re, Complex.inv_re, Complex.inv_im, Complex.normSq, Complex.div_re,
    Complex.div_im]
  field_simp
  rw [show (Real.sqrt d) ^ 2 = d by rw [sq]; exact hsq] at *
  ring
end PI.UnitaryGroupMassFormula.UnimodLocStd
