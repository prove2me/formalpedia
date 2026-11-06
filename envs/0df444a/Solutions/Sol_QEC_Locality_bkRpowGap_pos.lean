-- Prove2me | solution 1 for QEC.Locality.bkRpowGap_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:08:14.800552+00:00
-- url     : https://prove2.me/submissions/bd57021c-4319-4489-88a0-36b6024f8c52

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
theorem _root_.solution {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) :
    0 < bkRpowGap c := by
  rcases hc0.eq_or_lt with rfl | hc0
  · norm_num [bkRpowGap]
  · have hthird : (1 / 3 : ℝ) < (1 / 3 : ℝ) ^ c :=
      Real.self_lt_rpow_of_lt_one (by norm_num) (by norm_num) hc1
    have htwoThirds : (2 / 3 : ℝ) < (2 / 3 : ℝ) ^ c :=
      Real.self_lt_rpow_of_lt_one (by norm_num) (by norm_num) hc1
    unfold bkRpowGap
    linarith
end QEC.Locality
