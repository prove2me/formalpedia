-- Prove2me | solution 1 for SoficGroups.ErshovJaikinFiniteSpectral.norm_inner_le_inv_sqrt_eight_of_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:54.580336+00:00
-- url     : https://prove2.me/submissions/a3af22db-0fbd-451c-85f9-f6d591021e1b

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.ErshovJaikinFiniteSpectral
open Filter Topology
universe u v
namespace SoficGroups.ErshovJaikinFiniteSpectral
theorem _root_.solution
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (a b : H)
    (h : 8 * ‖inner ℂ a b‖ ^ 2 ≤ ‖a‖ ^ 2 * ‖b‖ ^ 2) :
    ‖inner ℂ a b‖ ≤
      (Real.sqrt (8 : ℝ))⁻¹ * ‖a‖ * ‖b‖ := by
  have hsqrt : 0 < Real.sqrt (8 : ℝ) := by positivity
  have hsquare : Real.sqrt (8 : ℝ) ^ 2 = 8 :=
    Real.sq_sqrt (by norm_num)
  have hsq :
      ‖inner ℂ a b‖ ^ 2 ≤
        ((Real.sqrt (8 : ℝ))⁻¹ * ‖a‖ * ‖b‖) ^ 2 := by
    calc
      ‖inner ℂ a b‖ ^ 2 ≤
          (‖a‖ ^ 2 * ‖b‖ ^ 2) / 8 := by
            apply (le_div_iff₀ (show (0 : ℝ) < 8 by norm_num)).mpr
            nlinarith
      _ = ((Real.sqrt (8 : ℝ))⁻¹ * ‖a‖ * ‖b‖) ^ 2 := by
        field_simp
        nlinarith
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hsq
end SoficGroups.ErshovJaikinFiniteSpectral
