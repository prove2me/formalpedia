-- Prove2me | solution 1 for QEC.Locality.exists_inducedVertexSet_attaining_twoThirdsSeparationProfile
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:12:08.124673+00:00
-- url     : https://prove2.me/submissions/02d9988d-fb39-4070-bbba-1f7fe4dcdfc8

import Definitions.Def_QEC_Coding_Stabilizer_FixedGeneratorInteraction
import Definitions.Def_QEC_Locality_SeparatorProfile_Core

set_option autoImplicit false
open QEC QEC.Locality
universe u
namespace QEC.Locality
theorem _root_.solution
    {ι : Type u} [Fintype ι] [DecidableEq ι] (G : ConnectivityGraph ι) (scale : Nat) :
    ∃ vertices : Finset ι,
      vertices ⊆ Finset.univ ∧ vertices.card ≤ scale ∧
        minimumTwoThirdsBalancedVertexSeparatorSize G vertices =
          twoThirdsSeparationProfile G scale := by
  classical
  have hmem : twoThirdsSeparationProfile G scale ∈
      inducedMinimumTwoThirdsBalancedSeparatorSizes G scale := by
    exact Finset.max'_mem _ _
  rcases Finset.mem_image.1 hmem with ⟨vertices, hvertices, hvalue⟩
  rcases (mem_inducedVertexSetsAtMost_iff scale vertices).1 hvertices with ⟨hsubset, hcard⟩
  exact ⟨vertices, hsubset, hcard, hvalue⟩
end QEC.Locality
