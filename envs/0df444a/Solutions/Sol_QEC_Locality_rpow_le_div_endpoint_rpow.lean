-- Prove2me | solution 1 for QEC.Locality.rpow_le_div_endpoint_rpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:36:52.979266+00:00
-- url     : https://prove2.me/submissions/fd855622-6a49-4da5-8d5a-fa812106eaf0

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
    {a q c : ℝ} (ha : 0 < a) (haq : a ≤ q)
    (hc1 : c < 1) :
    q ^ c ≤ q / a ^ (1 - c) := by
  have hq : 0 < q := ha.trans_le haq
  have hp : 0 < 1 - c := sub_pos.mpr hc1
  have hpow : a ^ (1 - c) ≤ q ^ (1 - c) :=
    Real.rpow_le_rpow ha.le haq hp.le
  have haPowPos : 0 < a ^ (1 - c) := Real.rpow_pos_of_pos ha _
  apply (le_div_iff₀ haPowPos).2
  calc
    q ^ c * a ^ (1 - c) ≤ q ^ c * q ^ (1 - c) := by
      exact mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hq.le c)
    _ = q := by
      rw [← Real.rpow_add hq]
      ring_nf
      exact Real.rpow_one q
end QEC.Locality
