-- Prove2me | solution 1 for SumProduct.cubeSumLaw_Icc_eq_inv_pi_integral_re_charFun_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:14:19.280503+00:00
-- url     : https://prove2.me/submissions/c6fdc7d2-3d0a-435a-878c-b3992ef21b35

import Definitions.Def_SumProduct_CubeSection
import Definitions.Def_SumProduct_SincIntegral
import Mathlib.MeasureTheory.Measure.IntegralCharFun
import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_SumProduct_CubeSectionCore
import Theorems.Thm_SumProduct_cubeSumLawSuccDensity_zero_toReal
import Theorems.Thm_SumProduct_cubeSumLawSuccDensity_zero_eq_inv_two_pi_integral_re_charFun

set_option autoImplicit true
open MeasureTheory
open scoped ENNReal MeasureTheory FourierTransform
open SumProduct
noncomputable section
namespace SumProduct
theorem _root_.solution (n : ℕ) (_hn : 1 ≤ n) :
    (cubeSumLaw n (Set.Icc (-1 : ℝ) 1)).toReal =
      (Real.pi)⁻¹ * ∫ t : ℝ, (charFun (cubeSumLaw (n + 1)) t).re := by
  have hden := cubeSumLawSuccDensity_zero_toReal n
  have hfour := cubeSumLawSuccDensity_zero_eq_inv_two_pi_integral_re_charFun n _hn
  rw [hden] at hfour
  have hπ : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  calc
    (cubeSumLaw n (Set.Icc (-1 : ℝ) 1)).toReal =
        2 * ((1 / 2 : ℝ) * (cubeSumLaw n (Set.Icc (-1 : ℝ) 1)).toReal) := by ring
    _ = 2 * ((2 * Real.pi)⁻¹ * ∫ t : ℝ, (charFun (cubeSumLaw (n + 1)) t).re) := by
        rw [hfour]
    _ = (Real.pi)⁻¹ * ∫ t : ℝ, (charFun (cubeSumLaw (n + 1)) t).re := by
        field_simp [hπ]
end SumProduct
