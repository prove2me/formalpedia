-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_coordEmbed_apply_57a659e1152c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:54:06.708863+00:00
-- url     : https://prove2.me/submissions/e93b3989-b284-4ede-b6f7-4224887292b8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StCoordEmbedBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField Module
noncomputable section
variable (E : Type*) [Field E] [NumberField E] (ι : Type*) [Fintype ι]
omit [Fintype ι]
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
theorem _root_.solution (y : ι → E) (w : InfinitePlace E) (i : ι) :
    coordEmbed E ι y w i = w.embedding (y i) := rfl
end GroundTheory.Heights₂.Heights.FiniteCovolume
