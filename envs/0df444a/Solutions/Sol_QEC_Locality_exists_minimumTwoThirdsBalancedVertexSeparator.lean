-- Prove2me | solution 1 for QEC.Locality.exists_minimumTwoThirdsBalancedVertexSeparator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:58:12.168654+00:00
-- url     : https://prove2.me/submissions/2028ad3c-2e3a-49e1-bc91-dc864e8f71a8

import Definitions.Def_QEC_Coding_Stabilizer_FixedGeneratorInteraction
import Definitions.Def_QEC_Locality_SeparatorProfile_Core

set_option autoImplicit false
open QEC QEC.Locality
universe u
namespace QEC.Locality
theorem _root_.solution {ι : Type u} [Fintype ι] [DecidableEq ι]
    (G : ConnectivityGraph ι) (vertices : Finset ι) :
    ∃ separator : Finset ι,
      separator ⊆ vertices ∧
        IsTwoThirdsBalancedVertexSeparator G vertices separator ∧
        separator.card = minimumTwoThirdsBalancedVertexSeparatorSize G vertices := by
  classical
  have hmem : minimumTwoThirdsBalancedVertexSeparatorSize G vertices ∈
      twoThirdsBalancedSeparatorCardinalities G vertices := by
    exact Finset.min'_mem _ _
  rcases Finset.mem_image.1 hmem with ⟨separator, hseparator, hcard⟩
  rcases (mem_twoThirdsBalancedSeparatorCandidates_iff G vertices separator).1 hseparator with
    ⟨hsubset, hbalanced⟩
  exact ⟨separator, hsubset, hbalanced, hcard⟩
end QEC.Locality
