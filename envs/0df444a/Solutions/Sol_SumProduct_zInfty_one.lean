-- Prove2me | solution 1 for SumProduct.zInfty_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:02:46.20601+00:00
-- url     : https://prove2.me/submissions/afd6098c-70ef-4be1-a451-1245453c479d

import Definitions.Def_DedekindZeta_PerClass
import Definitions.Def_DedekindZeta_ConeMellinBridge
import Definitions.Def_SumProduct_PartialZetaMellin
import Theorems.Thm_SumProduct_zInfty_ofReal

set_option autoImplicit true
open scoped NumberField nonZeroDivisors
open MeasureTheory NumberField NumberField.InfinitePlace NumberField.Units
open SumProduct
variable (K : Type*) [Field K] [NumberField K]
namespace SumProduct
theorem _root_.solution :
    DedekindZeta.ZInfty K (1 : ℂ)
      = ((Real.sqrt |(NumberField.discr K : ℝ)|
          / Real.pi ^ NumberField.InfinitePlace.nrComplexPlaces K : ℝ) : ℂ) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  -- Use the realness lemma at `s = 1`.
  have h1 : ((1 : ℝ) : ℂ) = (1 : ℂ) := by norm_num
  rw [← h1, zInfty_ofReal K 1]
  congr 1
  -- Simplify the real prefactor at `s = 1`.
  -- `|d|^(1/2) = √|d|`.
  have hsqrt : |(NumberField.discr K : ℝ)| ^ ((1 : ℝ) / 2)
      = Real.sqrt |(NumberField.discr K : ℝ)| := by
    rw [Real.sqrt_eq_rpow]
  -- `LReal` factor `= 1`.
  have hLR : (Real.pi ^ (-((1 : ℝ) / 2)) * Real.Gamma ((1 : ℝ) / 2)) = 1 := by
    rw [Real.Gamma_one_half_eq, Real.sqrt_eq_rpow, ← Real.rpow_add hpi]
    norm_num
  -- `LComplex` factor `= 1/π`.
  have hLC : (2 * (2 * Real.pi) ^ (-(1 : ℝ)) * Real.Gamma 1) = 1 / Real.pi := by
    rw [Real.Gamma_one, Real.rpow_neg_one]
    field_simp
  rw [hsqrt, hLR, hLC, one_pow, mul_one, div_pow, one_pow, mul_one_div]
end SumProduct
