-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.newton_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:38:29.36225+00:00
-- url     : https://prove2.me/submissions/9820a8ad-555c-423e-a0c5-2f0d27f518c5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_KurDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_KurNewton
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_newton_expansion
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_newton_lipschitz
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_newton_derivative_coeff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open Formalism.L2.Th1.CM
variable {K : Type} [NormedField K] [IsUltrametricDist K]
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (P : Polynomial K) (hP : ∀ i, ‖P.coeff i‖ ≤ 1) (x : K) (hx : ‖x‖ ≤ 1)
    (h0 : ‖P.eval x‖ < 1) (h1 : ‖P.derivative.eval x‖ = 1) :
    ∃ y : K, ‖y‖ ≤ 1 ∧ ‖P.derivative.eval y‖ = 1 ∧ ‖P.eval y‖ ≤ ‖P.eval x‖ ^ 2 ∧
      ‖y - x‖ ≤ ‖P.eval x‖ := by
  have hd : P.derivative.eval x ≠ 0 := by
    intro h
    rw [h, norm_zero] at h1
    exact zero_ne_one h1
  set t : K := -(P.eval x / P.derivative.eval x) with ht
  have hnt : ‖t‖ = ‖P.eval x‖ := by rw [ht, norm_neg, norm_div, h1, div_one]
  have ht1 : ‖t‖ ≤ 1 := hnt ▸ h0.le
  have hy : ‖x + t‖ ≤ 1 := (IsUltrametricDist.norm_add_le_max x t).trans (max_le hx ht1)
  obtain ⟨k, hk, he⟩ := newton_expansion P hP x t hx ht1
  refine ⟨x + t, hy, ?_, ?_, ?_⟩
  · have hl := newton_lipschitz P.derivative (newton_derivative_coeff P hP) (x + t) x hy hx
    rw [add_sub_cancel_left, hnt] at hl
    have hlt : ‖P.derivative.eval (x + t) - P.derivative.eval x‖ < ‖P.derivative.eval x‖ := by
      rw [h1]; exact lt_of_le_of_lt hl h0
    have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne
    rw [sub_add_cancel, max_eq_right hlt.le, h1] at this
    exact this
  · have hz : P.eval x + P.derivative.eval x * t = 0 := by
      rw [ht]; field_simp; ring
    rw [he, hz, zero_add, norm_mul, norm_pow, hnt]
    exact mul_le_of_le_one_left (by positivity) hk
  · rw [add_sub_cancel_left, hnt]
end ReciprocityTheory.ChartRestriction.L1
