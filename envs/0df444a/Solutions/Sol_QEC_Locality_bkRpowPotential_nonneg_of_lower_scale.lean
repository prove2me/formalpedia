-- Prove2me | solution 1 for QEC.Locality.bkRpowPotential_nonneg_of_lower_scale
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:26:32.061633+00:00
-- url     : https://prove2.me/submissions/c85eaf31-b451-4ce7-9c29-8c58a65bf136

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_SumPreservingRecurrence
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_QuantitativeRecurrence
import Theorems.Thm_QEC_Locality_rpow_le_div_endpoint_rpow
import Theorems.Thm_QEC_Locality_beta_div_bkRpowGap_nonneg

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open Set
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution
    {beta c : ℝ} {d child : Nat}
    (hbeta : 0 ≤ beta) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hd : 0 < d) (hlower : d ≤ 3 * child) :
    0 ≤ bkRpowPotential beta c d child := by
  have hdReal : (0 : ℝ) < d := by exact_mod_cast hd
  have hratio : (1 / 3 : ℝ) ≤ (child : ℝ) / d := by
    apply (le_div_iff₀ hdReal).2
    have hlowerReal : (d : ℝ) ≤ 3 * child := by exact_mod_cast hlower
    nlinarith
  have hpower := rpow_le_div_endpoint_rpow
    (a := (1 / 3 : ℝ)) (q := (child : ℝ) / d) (c := c)
    (by norm_num) hratio hc1
  unfold bkRpowPotential
  exact mul_nonneg
    (mul_nonneg (beta_div_bkRpowGap_nonneg hbeta hc0 hc1)
      (Real.rpow_nonneg hdReal.le c))
    (sub_nonneg.mpr hpower)
end QEC.Locality
