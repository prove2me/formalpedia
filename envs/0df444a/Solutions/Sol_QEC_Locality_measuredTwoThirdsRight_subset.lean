-- Prove2me | solution 1 for QEC.Locality.measuredTwoThirdsRight_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:12:16.148981+00:00
-- url     : https://prove2.me/submissions/5688c5ad-037e-4fa7-b12d-3a034a55a496

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
    measuredTwoThirdsRight G vertices ⊆ vertices := by
  intro x hx
  have hsplit := measuredTwoThirdsSplit_spec G vertices
  have hxDiff : x ∈ vertices \ measuredTwoThirdsSeparator G vertices := by
    rw [← hsplit.2.1]
    exact Finset.mem_union_right _ hx
  exact (Finset.mem_sdiff.mp hxDiff).1
end QEC.Locality
