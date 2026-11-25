-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.rep_area_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:47:36.740898+00:00
-- url     : https://prove2.me/submissions/a54c9c8d-a24d-4560-a971-60eae9fa3c4f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepArith
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepHSelfInt
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_rep_omega1
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_rep_omega2


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
theorem _root_.solution : area (cmL a b d ha hd lam hlam) = Complex.normSq lam * a * (Real.sqrt d / 2) := by
  rw [area, rep_omega1, rep_omega2]
  have hθ : (cmTheta b d).im = Real.sqrt d / 2 := by
    simp [cmTheta]
  have e : conj (lam * (a : ℂ)) * (lam * cmTheta b d) =
      ((Complex.normSq lam * a : ℝ) : ℂ) * cmTheta b d := by
    rw [map_mul, Complex.conj_natCast]
    push_cast
    rw [Complex.normSq_eq_conj_mul_self]
    ring
  rw [e, Complex.im_ofReal_mul, hθ, abs_of_nonneg]
  exact mul_nonneg (mul_nonneg (Complex.normSq_nonneg _) (Nat.cast_nonneg _))
    (div_nonneg (Real.sqrt_nonneg _) zero_le_two)
end PI.UnitaryGroupMassFormula.UnimodLocStd
