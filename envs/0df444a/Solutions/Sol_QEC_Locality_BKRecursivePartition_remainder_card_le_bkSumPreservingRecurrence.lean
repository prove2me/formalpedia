-- Prove2me | solution 1 for QEC.Locality.BKRecursivePartition.remainder_card_le_bkSumPreservingRecurrence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:33:05.797276+00:00
-- url     : https://prove2.me/submissions/fc627c02-b5b3-4833-82dc-e2335e565301

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_RecursiveSeparator
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_MaxFamily
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_SumPreservingRecurrence
import Theorems.Thm_QEC_Locality_bkSeparatorRecurrence_le_bkSumPreservingRecurrence_card

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
    partition.remainder.card ≤ bkSumPreservingRecurrence G d vertices.card :=
  partition.remainder_card_le.trans
    (bkSeparatorRecurrence_le_bkSumPreservingRecurrence_card G d vertices)
end BKRecursivePartition
end QEC.Locality
