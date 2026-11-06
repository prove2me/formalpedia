-- Prove2me | solution 1 for QEC.Locality.measuredTwoThirdsLeft_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:12:09.842118+00:00
-- url     : https://prove2.me/submissions/afac77e9-59e0-48fd-9df9-c80f16389d54

import Definitions.Def_QEC_Locality_SeparatorProfile_Core
import Definitions.Def_QEC_Locality_CorrectableRegions_SemanticDistanceErasure
import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_RecursiveSeparator

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open QEC Semantics Coding
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution
    (G : ConnectivityGraph ι) (vertices : Finset ι) :
    measuredTwoThirdsLeft G vertices ⊆ vertices := by
  intro x hx
  have hsplit := measuredTwoThirdsSplit_spec G vertices
  have hxDiff : x ∈ vertices \ measuredTwoThirdsSeparator G vertices := by
    rw [← hsplit.2.1]
    exact Finset.mem_union_left _ hx
  exact (Finset.mem_sdiff.mp hxDiff).1
end QEC.Locality
