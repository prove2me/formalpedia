-- Prove2me | solution 1 for QEC.Locality.minimumTwoThirdsBalancedVertexSeparatorSize_le_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:09:43.977396+00:00
-- url     : https://prove2.me/submissions/3e4d59ca-555e-416e-942d-c0c5c29fad7a

import Definitions.Def_QEC_Coding_Stabilizer_FixedGeneratorInteraction
import Definitions.Def_QEC_Locality_SeparatorProfile_Core

set_option autoImplicit false
open QEC QEC.Locality
universe u
namespace QEC.Locality
theorem _root_.solution {ι : Type u} [Fintype ι] [DecidableEq ι]
    (G : ConnectivityGraph ι) (vertices separator : Finset ι)
    (hsubset : separator ⊆ vertices)
    (hbalanced : IsTwoThirdsBalancedVertexSeparator G vertices separator) :
    minimumTwoThirdsBalancedVertexSeparatorSize G vertices ≤ separator.card := by
  classical
  apply Finset.min'_le
  exact Finset.mem_image.2 ⟨separator,
    (mem_twoThirdsBalancedSeparatorCandidates_iff G vertices separator).2
      ⟨hsubset, hbalanced⟩, rfl⟩
end QEC.Locality
