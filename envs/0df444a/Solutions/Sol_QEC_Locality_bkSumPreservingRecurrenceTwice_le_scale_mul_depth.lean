-- Prove2me | solution 1 for QEC.Locality.bkSumPreservingRecurrenceTwice_le_scale_mul_depth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:14:08.58051+00:00
-- url     : https://prove2.me/submissions/139c35cf-fbb1-4788-bd45-418463a32a23

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_RecursiveSeparator
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_MaxFamily
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_SumPreservingRecurrence
import Theorems.Thm_QEC_Locality_bkSumPreservingRecurrence_le_scale_mul_depth

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution
    (G : ConnectivityGraph ι) (d parent : Nat) :
    bkSumPreservingRecurrenceTwice G d parent ≤
      bkSumPreservingRecurrence G d parent *
        bkTwoThirdsDepth d (bkSumPreservingRecurrence G d parent) := by
  exact bkSumPreservingRecurrence_le_scale_mul_depth G d
    (bkSumPreservingRecurrence G d parent)
end QEC.Locality
