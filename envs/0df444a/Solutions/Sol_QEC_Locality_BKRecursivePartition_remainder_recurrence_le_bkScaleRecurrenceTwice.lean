-- Prove2me | solution 1 for QEC.Locality.BKRecursivePartition.remainder_recurrence_le_bkScaleRecurrenceTwice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:12:54.603167+00:00
-- url     : https://prove2.me/submissions/bebc2364-b03b-4ffa-9c4d-389a910e6008

import Definitions.Def_QEC_Locality_SeparatorProfile_Core
import Definitions.Def_QEC_Locality_CorrectableRegions_SemanticDistanceErasure
import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_RecursiveSeparator
import Theorems.Thm_QEC_Locality_bkSeparatorRecurrence_le_bkScaleRecurrence
import Theorems.Thm_QEC_Locality_BKRecursivePartition_remainder_card_le_bkScaleRecurrence

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open QEC Semantics Coding
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
namespace BKRecursivePartition
theorem _root_.solution
    {G : ConnectivityGraph ι} {d : Nat} {vertices : Finset ι}
    (partition : BKRecursivePartition G d vertices) (r : Nat)
    (hvertices : vertices.card ≤ r) :
    bkSeparatorRecurrence G d partition.remainder ≤ bkScaleRecurrenceTwice G d r := by
  exact bkSeparatorRecurrence_le_bkScaleRecurrence G d partition.remainder
    (bkScaleRecurrence G d r)
    (partition.remainder_card_le_bkScaleRecurrence r hvertices)
end BKRecursivePartition
end QEC.Locality
