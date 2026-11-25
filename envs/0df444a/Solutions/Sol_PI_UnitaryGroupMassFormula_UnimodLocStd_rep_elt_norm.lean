-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.rep_elt_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:55:09.037175+00:00
-- url     : https://prove2.me/submissions/c5f4d893-b85d-4895-ad1e-7b3d9e95cdce

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepArith
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_rep_theta_add_conj
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_rep_theta_mul_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS
variable (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0)
namespace PI.UnitaryGroupMassFormula.UnimodLocStd
theorem _root_.solution (hOK : 4 * (a : ℤ) * c = b ^ 2 + d) (p q : ℤ) :
    (lam * ((p : ℂ) * a + q * cmTheta b d)) * conj (lam * ((p : ℂ) * a + q * cmTheta b d)) =
      (Complex.normSq lam : ℂ) * a * ((a * p ^ 2 + b * p * q + c * q ^ 2 : ℤ) : ℂ) := by
  have h1 := rep_theta_add_conj b d
  have h2 := rep_theta_mul_conj a b c d hOK
  have hN := Complex.mul_conj lam
  simp only [map_mul, map_add, map_intCast, map_natCast]
  push_cast
  linear_combination ((p : ℂ) * a + q * cmTheta b d) * ((p : ℂ) * a + q * conj (cmTheta b d)) * hN +
    (Complex.normSq lam : ℂ) * p * q * a * h1 + (Complex.normSq lam : ℂ) * q ^ 2 * h2
end PI.UnitaryGroupMassFormula.UnimodLocStd
