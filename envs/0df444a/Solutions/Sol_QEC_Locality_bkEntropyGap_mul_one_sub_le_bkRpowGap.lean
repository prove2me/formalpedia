-- Prove2me | solution 1 for QEC.Locality.bkEntropyGap_mul_one_sub_le_bkRpowGap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:29:55.495461+00:00
-- url     : https://prove2.me/submissions/2815fcca-98e8-4b08-a6e1-dffdbb01091f

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_SumPreservingRecurrence
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_QuantitativeRecurrence
import Theorems.Thm_QEC_Locality_neg_mul_log_mul_one_sub_le_rpow_sub

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open Set
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution (c : ℝ) :
    bkEntropyGap * (1 - c) ≤ bkRpowGap c := by
  have htwo := neg_mul_log_mul_one_sub_le_rpow_sub
    (c := c) (show (0 : ℝ) < 2 / 3 by norm_num)
  have hone := neg_mul_log_mul_one_sub_le_rpow_sub
    (c := c) (show (0 : ℝ) < 1 / 3 by norm_num)
  unfold bkEntropyGap bkRpowGap
  nlinarith
end QEC.Locality
