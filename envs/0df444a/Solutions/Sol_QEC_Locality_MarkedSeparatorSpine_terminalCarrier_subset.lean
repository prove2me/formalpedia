-- Prove2me | solution 1 for QEC.Locality.MarkedSeparatorSpine.terminalCarrier_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:16:40.67402+00:00
-- url     : https://prove2.me/submissions/214a11da-12fb-489a-b6c3-2f42764351d7

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_RecursiveSeparator
import Definitions.Def_QEC_Locality_SeparatorProfile_Quantitative
import Definitions.Def_QEC_Locality_SeparatorProfile_Weighted
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans

section
namespace QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
private theorem markedSpine_left_subset
    {G : ConnectivityGraph ι} {vertices left separator right : Finset ι}
    (hpartition : TwoThirdsBalancedPartitionAfterDeleting G vertices left separator right) :
    left ⊆ vertices := by
  intro x hx
  exact (Finset.mem_sdiff.mp (by rw [← hpartition.2.1]; exact Finset.mem_union_left _ hx)).1
private theorem markedSpine_right_subset
    {G : ConnectivityGraph ι} {vertices left separator right : Finset ι}
    (hpartition : TwoThirdsBalancedPartitionAfterDeleting G vertices left separator right) :
    right ⊆ vertices := by
  intro x hx
  exact (Finset.mem_sdiff.mp (by rw [← hpartition.2.1]; exact Finset.mem_union_right _ hx)).1
end QEC.Locality
end

set_option autoImplicit false
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
namespace MarkedSeparatorSpine
theorem _root_.solution
    {G : ConnectivityGraph ι} {marked vertices : Finset ι}
    (spine : MarkedSeparatorSpine G marked vertices) :
    spine.terminalCarrier ⊆ vertices := by
  induction spine with
  | stop hpartition hminimum hleftLight hrightLight => exact Finset.Subset.rfl
  | followLeft hpartition hminimum hleftHeavy subtree ih =>
      exact ih.trans (markedSpine_left_subset hpartition)
  | followRight hpartition hminimum hrightHeavy subtree ih =>
      exact ih.trans (markedSpine_right_subset hpartition)
end MarkedSeparatorSpine
end QEC.Locality
