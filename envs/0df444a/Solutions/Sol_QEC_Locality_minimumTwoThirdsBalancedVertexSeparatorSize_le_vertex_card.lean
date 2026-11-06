-- Prove2me | solution 1 for QEC.Locality.minimumTwoThirdsBalancedVertexSeparatorSize_le_vertex_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:30:42.471207+00:00
-- url     : https://prove2.me/submissions/adaaae25-44a4-44a7-bc3b-f48abb3af110

import Definitions.Def_QEC_Coding_Stabilizer_FixedGeneratorInteraction
import Definitions.Def_QEC_Locality_SeparatorProfile_Core
import Theorems.Thm_QEC_Locality_minimumTwoThirdsBalancedVertexSeparatorSize_le_card
import Theorems.Thm_QEC_Locality_self_isTwoThirdsBalancedVertexSeparator


set_option autoImplicit false
open QEC QEC.Locality
universe u
namespace QEC.Locality
theorem _root_.solution {ι : Type u} [Fintype ι] [DecidableEq ι]
    (G : ConnectivityGraph ι) (vertices : Finset ι) :
    minimumTwoThirdsBalancedVertexSeparatorSize G vertices ≤ vertices.card :=
  minimumTwoThirdsBalancedVertexSeparatorSize_le_card G vertices vertices subset_rfl
    (self_isTwoThirdsBalancedVertexSeparator G vertices)
end QEC.Locality
