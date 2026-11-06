-- Prove2me | solution 1 for QEC.Locality.weightedSpineSeparatorBudget_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:31:49.759119+00:00
-- url     : https://prove2.me/submissions/b3dc287e-810f-4912-9c75-176243e244c7

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_RecursiveSeparator
import Definitions.Def_QEC_Locality_SeparatorProfile_Quantitative
import Definitions.Def_QEC_Locality_SeparatorProfile_Weighted
import Theorems.Thm_QEC_Locality_markedSpineDecayRatio_lt_one

set_option autoImplicit false
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution
    {beta exponent : ℝ} (hbeta : 1 ≤ beta) (hexponent : 0 < exponent)
    {r : Nat} (hr : 1 ≤ r) :
    0 < weightedSpineSeparatorBudget beta exponent r := by
  rw [weightedSpineSeparatorBudget, Nat.ceil_pos]
  have hdenominator : 0 < 1 - markedSpineDecayRatio exponent :=
    sub_pos.mpr (markedSpineDecayRatio_lt_one hexponent)
  exact mul_pos (div_pos (zero_lt_one.trans_le hbeta) hdenominator)
    (Real.rpow_pos_of_pos (by exact_mod_cast hr) exponent)
end QEC.Locality
