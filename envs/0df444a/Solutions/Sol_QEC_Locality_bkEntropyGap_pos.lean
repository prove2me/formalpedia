-- Prove2me | solution 1 for QEC.Locality.bkEntropyGap_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:08:15.49391+00:00
-- url     : https://prove2.me/submissions/b0d2682e-0a6d-4385-8099-0f4737a78d67

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
theorem _root_.solution : 0 < bkEntropyGap := by
  have hlogThird : Real.log (1 / 3 : ℝ) < 0 := Real.log_neg (by norm_num) (by norm_num)
  have hlogTwoThirds : Real.log (2 / 3 : ℝ) < 0 :=
    Real.log_neg (by norm_num) (by norm_num)
  unfold bkEntropyGap
  nlinarith
end QEC.Locality
