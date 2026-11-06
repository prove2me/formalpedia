-- Prove2me | solution 1 for QEC.Locality.twoThirdsSeparationProfile_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:29:57.716713+00:00
-- url     : https://prove2.me/submissions/049fee2c-b972-401c-8c9f-035f886d7b99

import Definitions.Def_QEC_Coding_Stabilizer_FixedGeneratorInteraction
import Definitions.Def_QEC_Locality_SeparatorProfile_Core
import Theorems.Thm_QEC_Locality_minimumTwoThirdsBalancedVertexSeparatorSize_le_twoThirdsSeparationProfile

set_option autoImplicit false
open QEC QEC.Locality
universe u
namespace QEC.Locality
theorem _root_.solution {ι : Type u} [Fintype ι] [DecidableEq ι]
    (G : ConnectivityGraph ι) {small large : Nat} (hscale : small ≤ large) :
    twoThirdsSeparationProfile G small ≤ twoThirdsSeparationProfile G large := by
  classical
  apply Finset.max'_le
  intro size hsize
  rcases Finset.mem_image.1 hsize with ⟨vertices, hvertices, hvalue⟩
  rw [← hvalue]
  have hsmallVertices := (mem_inducedVertexSetsAtMost_iff small vertices).1 hvertices
  exact minimumTwoThirdsBalancedVertexSeparatorSize_le_twoThirdsSeparationProfile
    G large vertices hsmallVertices.1 (hsmallVertices.2.trans hscale)
end QEC.Locality
