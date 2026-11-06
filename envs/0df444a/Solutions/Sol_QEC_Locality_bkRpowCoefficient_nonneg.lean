-- Prove2me | solution 1 for QEC.Locality.bkRpowCoefficient_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:26:31.08732+00:00
-- url     : https://prove2.me/submissions/a6b401b1-8ccd-4fff-a83c-bc1b3a2ef053

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_SumPreservingRecurrence
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_QuantitativeRecurrence
import Theorems.Thm_QEC_Locality_bkRpowGap_pos

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open Set
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution
    {beta c : ℝ} (hbeta : 0 ≤ beta) (hc0 : 0 ≤ c) (hc1 : c < 1) :
    0 ≤ bkRpowCoefficient beta c := by
  unfold bkRpowCoefficient
  exact div_nonneg hbeta (mul_nonneg (bkRpowGap_pos hc0 hc1).le
    (Real.rpow_nonneg (by norm_num) _))
end QEC.Locality
