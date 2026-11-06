-- Prove2me | solution 1 for QEC.Locality.minimumTwoThirdsBalancedVertexSeparatorSize_le_twoThirdsSeparationProfile
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:58:06.540072+00:00
-- url     : https://prove2.me/submissions/4a215274-f0b9-4dba-98cd-9b7cb2d76a3f

import Definitions.Def_QEC_Coding_Stabilizer_FixedGeneratorInteraction
import Definitions.Def_QEC_Locality_SeparatorProfile_Core

set_option autoImplicit false
open QEC QEC.Locality
universe u
namespace QEC.Locality
theorem _root_.solution
    {ι : Type u} [Fintype ι] [DecidableEq ι] (G : ConnectivityGraph ι) (scale : Nat) (vertices : Finset ι)
    (hsubset : vertices ⊆ Finset.univ) (hcard : vertices.card ≤ scale) :
    minimumTwoThirdsBalancedVertexSeparatorSize G vertices ≤
      twoThirdsSeparationProfile G scale := by
  classical
  apply Finset.le_max'
  exact Finset.mem_image.2 ⟨vertices,
    (mem_inducedVertexSetsAtMost_iff scale vertices).2 ⟨hsubset, hcard⟩, rfl⟩
end QEC.Locality
