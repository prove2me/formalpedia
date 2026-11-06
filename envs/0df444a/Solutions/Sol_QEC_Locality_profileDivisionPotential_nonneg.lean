-- Prove2me | solution 1 for QEC.Locality.profileDivisionPotential_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:30:53.918027+00:00
-- url     : https://prove2.me/submissions/d527cf25-8928-4c10-9e93-9fb2b0950e60

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_QuantitativeRecurrence
import Definitions.Def_QEC_Locality_SeparatorProfile_Quantitative
import Definitions.Def_QEC_Locality_SeparatorProfile_DivisionPotential
import Theorems.Thm_QEC_Locality_profileDivisionPotentialCoefficient_nonneg
import Theorems.Thm_QEC_Locality_rpow_le_div_endpoint_rpow


set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
namespace QEC.Locality
theorem _root_.solution
    {beta exponent : ℝ} {r parent : Nat}
    (hbeta : 0 ≤ beta) (hexponent : 0 < exponent ∧ exponent < 1)
    (hr : 0 < r) (hlower : r ≤ 4 * parent) :
    0 ≤ profileDivisionPotential beta exponent r parent := by
  have hrReal : (0 : ℝ) < r := by exact_mod_cast hr
  have hratio : (1 / 4 : ℝ) ≤ (parent : ℝ) / r := by
    apply (le_div_iff₀ hrReal).2
    have hlowerReal : (r : ℝ) ≤ 4 * parent := by exact_mod_cast hlower
    nlinarith
  have hpower := rpow_le_div_endpoint_rpow
    (a := (1 / 4 : ℝ)) (q := (parent : ℝ) / r) (c := exponent)
    (by norm_num) hratio hexponent.2
  unfold profileDivisionPotential
  exact mul_nonneg
    (mul_nonneg
      (profileDivisionPotentialCoefficient_nonneg hbeta hexponent)
      (Real.rpow_nonneg hrReal.le exponent))
    (sub_nonneg.mpr hpower)
end QEC.Locality
