-- Prove2me | solution 1 for QEC.Locality.neg_mul_log_mul_one_sub_le_rpow_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:26:22.444941+00:00
-- url     : https://prove2.me/submissions/1b389c98-8571-4e24-8888-bedc963433a1

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_SumPreservingRecurrence
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_QuantitativeRecurrence

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open Set
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution
    {base c : ℝ} (hbase : 0 < base) :
    -base * Real.log base * (1 - c) ≤ base ^ c - base := by
  have hexp := mul_le_mul_of_nonneg_left
    (Real.add_one_le_exp ((c - 1) * Real.log base)) hbase.le
  have hrpow : base ^ c = base * Real.exp ((c - 1) * Real.log base) := by
    calc
      base ^ c = base ^ (1 + (c - 1)) := by ring_nf
      _ = base ^ (1 : ℝ) * base ^ (c - 1) := Real.rpow_add hbase 1 (c - 1)
      _ = base * Real.exp (Real.log base * (c - 1)) := by
        rw [Real.rpow_one, Real.rpow_def_of_pos hbase]
      _ = base * Real.exp ((c - 1) * Real.log base) := by ring_nf
  rw [← hrpow] at hexp
  nlinarith
end QEC.Locality
