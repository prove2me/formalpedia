-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_embeddingBasisOfTotallyComplex_apply_45c8d02f06ce
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:11:23.15091+00:00
-- url     : https://prove2.me/submissions/0df8d5e8-16e0-4c16-a43d-6e6289c0612c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StCoordEmbedBasis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PCoordEmbedBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField Module NumberField.InfinitePlace NumberField.mixedEmbedding
noncomputable section
variable (E : Type*) [Field E] [NumberField E] (ι : Type*) [Fintype ι]
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
theorem _root_.solution [IsTotallyComplex E]
    (j : Free.ChooseBasisIndex ℤ (𝓞 E)) (w : InfinitePlace E) :
    embeddingBasisOfTotallyComplex E j w = w.embedding (integralBasis E j) := by
  rw [embeddingBasisOfTotallyComplex, Basis.map_apply, latticeBasis_apply]
  exact mixedEmbedding_apply_isComplex _ _ ⟨w, IsTotallyComplex.isComplex w⟩
end GroundTheory.Heights₂.Heights.FiniteCovolume
