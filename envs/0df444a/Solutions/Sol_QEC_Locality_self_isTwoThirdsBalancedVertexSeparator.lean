-- Prove2me | solution 1 for QEC.Locality.self_isTwoThirdsBalancedVertexSeparator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:32:38.494685+00:00
-- url     : https://prove2.me/submissions/63119407-b2aa-40c1-aeac-f0f3063e669f

import Mathlib
import Definitions.Def_QEC_Locality_Graph_Core

set_option autoImplicit false
open QEC QEC.Locality
universe u
namespace QEC.Locality
theorem _root_.solution {ι : Type u} [Fintype ι] [DecidableEq ι]
    (G : ConnectivityGraph ι) (vertices : Finset ι) :
    IsTwoThirdsBalancedVertexSeparator G vertices vertices := by
  refine ⟨∅, ∅, ?_⟩
  simp [TwoThirdsBalancedPartitionAfterDeleting, NoEdgeBetween]
end QEC.Locality
