-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.rep_area_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:50:56.179114+00:00
-- url     : https://prove2.me/submissions/c9cd9337-1436-453e-9d45-240bfc8993aa

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepArith
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
theorem _root_.solution : area (cmL a b d ha hd lam hlam) ≠ 0 := by
  rw [area, rep_omega1, rep_omega2, abs_ne_zero]
  have him : (conj (lam * a) * (lam * cmTheta b d)).im =
      Complex.normSq lam * a * (Real.sqrt d / 2) := by
    rw [show conj (lam * a) * (lam * cmTheta b d) = (lam * conj lam) * a * cmTheta b d by
      simp only [map_mul, map_natCast]; ring, Complex.mul_conj,
      show ((Complex.normSq lam : ℝ) : ℂ) * a * cmTheta b d =
        ((Complex.normSq lam * a : ℝ) : ℂ) * cmTheta b d by push_cast; ring, Complex.im_ofReal_mul]
    simp [cmTheta]
  rw [him]
  exact ne_of_gt (mul_pos (mul_pos (Complex.normSq_pos.2 hlam) (Nat.cast_pos.2 ha))
    (div_pos (Real.sqrt_pos.2 (Nat.cast_pos.2 hd)) two_pos))
end PI.UnitaryGroupMassFormula.UnimodLocStd
