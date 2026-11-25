-- Prove2me | solution 1 for PI.QmIndepW.indepC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:19:03.697836+00:00
-- url     : https://prove2.me/submissions/84bbae81-5d68-4f79-951c-faa6ebef9dda

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuarticIndependence_IndepC
import Theorems.Thm_PI_QmIndepW_ray

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.QmIndepW
open Complex
namespace PI.QmIndepW
theorem _root_.solution : IndepC := by
  intro y00 y10 y20 y01 y11 y21 y02 y12 y22 hyp
  obtain ⟨A1, B1, C1, D1, E1⟩ := ray _ _ _ _ _ _ _ _ _ hyp 1 1 one_ne_zero (by simp)
  obtain ⟨-, B2, C2, D2, -⟩ := ray _ _ _ _ _ _ _ _ _ hyp I (-I) I_ne_zero (by simp)
  obtain ⟨-, -, C3, -, -⟩ := ray _ _ _ _ _ _ _ _ _ hyp (1 + I) (1 - I)
    (by intro h; have := congrArg Complex.re h; simp at this) (by simp [sub_eq_add_neg])
  have h2I : (2 : ℂ) * I ≠ 0 := mul_ne_zero two_ne_zero I_ne_zero
  have h4I : (4 : ℂ) * I ≠ 0 := mul_ne_zero (by norm_num) I_ne_zero
  have y01z : y01 = 0 := by
    have : (2 * I) * y01 = 0 := by linear_combination I * B1 - B2
    exact (mul_eq_zero.mp this).resolve_left h2I
  have y10z : y10 = 0 := by linear_combination B1 - y01z
  have y12z : y12 = 0 := by
    have : (2 * I) * y12 = 0 := by linear_combination I * D1 - D2 + (I * y12 - I * y21) * I_sq
    exact (mul_eq_zero.mp this).resolve_left h2I
  have y21z : y21 = 0 := by linear_combination D1 - y12z
  have y11z : y11 = 0 := by
    have : (2 : ℂ) * y11 = 0 := by linear_combination C1 + C2 + (y11 - y20 - y02) * I_sq
    exact (mul_eq_zero.mp this).resolve_left two_ne_zero
  have y20z : y20 = 0 := by
    have : (4 * I) * y20 = 0 := by
      linear_combination C3 - (y20 - y11 + y02) * I_sq + 2 * I * C1 - (2 + 2 * I) * y11z
    exact (mul_eq_zero.mp this).resolve_left h4I
  have y02z : y02 = 0 := by linear_combination C1 - y11z - y20z
  have y22z : y22 = 0 := by linear_combination E1
  exact ⟨A1, y10z, y20z, y01z, y11z, y21z, y02z, y12z, y22z⟩
end PI.QmIndepW
