-- Prove2me | solution 1 for QEC.Locality.BKRecursivePartition.remainder_recurrence_le_bkSumPreservingRecurrenceTwice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:13:56.870683+00:00
-- url     : https://prove2.me/submissions/df49c0c8-c354-45e9-9718-b1647a7c4c7c

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_RecursiveSeparator
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_MaxFamily
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_SumPreservingRecurrence
import Theorems.Thm_QEC_Locality_bkSeparatorRecurrence_le_bkSumPreservingRecurrence_card
import Theorems.Thm_QEC_Locality_BKRecursivePartition_remainder_card_le_bkSumPreservingRecurrence
import Theorems.Thm_QEC_Locality_bkSumPreservingRecurrence_mono

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
namespace BKRecursivePartition
theorem _root_.solution
    {G : ConnectivityGraph ι} {d : Nat} {vertices : Finset ι}
    (partition : BKRecursivePartition G d vertices) :
    bkSeparatorRecurrence G d partition.remainder ≤
      bkSumPreservingRecurrenceTwice G d vertices.card := by
  exact (bkSeparatorRecurrence_le_bkSumPreservingRecurrence_card
      G d partition.remainder).trans
    (bkSumPreservingRecurrence_mono G d
      partition.remainder_card_le_bkSumPreservingRecurrence)
end BKRecursivePartition
end QEC.Locality
