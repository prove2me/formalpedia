-- Prove2me | solution 1 for PI.WMI.MMap.real_eq_of_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:09:58.595955+00:00
-- url     : https://prove2.me/submissions/08e6d69e-9e0e-42bd-8d5b-2eaf17021a6a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_IsPolyMon
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_ModelMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WMI
open PI.UpqRep Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial Matrix
open scoped InnerProductSpace
open PI.WMI.MMap
namespace PI.WMI.MMap
theorem _root_.solution {d c : ℝ}
    (h : ∀ τ : ℝ, Complex.exp (((τ * d : ℝ) : ℂ) * Complex.I) = Complex.exp (((τ * c : ℝ) : ℂ) * Complex.I)) :
    d = c := by
  by_contra hne
  have hk : d - c ≠ 0 := sub_ne_zero.mpr hne
  have h1 := h (Real.pi / (d - c))
  have h2 : Complex.exp (((Real.pi / (d - c) * d : ℝ) : ℂ) * Complex.I -
      ((Real.pi / (d - c) * c : ℝ) : ℂ) * Complex.I) = 1 := by
    rw [Complex.exp_sub, h1, div_self (Complex.exp_ne_zero _)]
  have h3 : ((Real.pi / (d - c) * d : ℝ) : ℂ) * Complex.I - ((Real.pi / (d - c) * c : ℝ) : ℂ) * Complex.I =
      (Real.pi : ℂ) * Complex.I := by
    rw [← sub_mul]
    congr 1
    rw [← Complex.ofReal_sub]
    congr 1
    field_simp
  rw [h3, Complex.exp_pi_mul_I] at h2
  norm_num at h2
end PI.WMI.MMap
