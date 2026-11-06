-- Prove2me | solution 1 for QEC.Locality.BKRecursivePartition.remainder_card_le_bkScaleRecurrence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:28:25.587891+00:00
-- url     : https://prove2.me/submissions/f65e6f73-439e-49cd-8db6-8cb6866e2817

import Definitions.Def_QEC_Locality_SeparatorProfile_Core
import Definitions.Def_QEC_Locality_CorrectableRegions_SemanticDistanceErasure
import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_RecursiveSeparator
import Theorems.Thm_QEC_Locality_bkSeparatorRecurrence_le_bkScaleRecurrence

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
    partition.remainder.card ≤ bkScaleRecurrence G d r :=
  partition.remainder_card_le.trans
    (bkSeparatorRecurrence_le_bkScaleRecurrence G d vertices r hvertices)
end BKRecursivePartition
end QEC.Locality
