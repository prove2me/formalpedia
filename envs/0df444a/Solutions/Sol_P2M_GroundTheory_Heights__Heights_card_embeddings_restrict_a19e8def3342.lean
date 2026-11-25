-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_card_embeddings_restrict_a19e8def3342
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:19:39.839358+00:00
-- url     : https://prove2.me/submissions/63f2874e-9d18-4556-96c1-37fd2e6c5fe3

import Theorems.Thm_P2M_UpperTheory_Reformulated_B_CardEmbeddingsRestrict_card_embeddings_restrict__3e5c16d106ca
import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CardEmbeddingsRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FieldChange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField Module
noncomputable section
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
open Classical
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (τ : K →+* ℂ) :
    (Finset.univ.filter fun σ : L →+* ℂ ↦ σ.comp (algebraMap K L) = τ).card = finrank K L :=
  _root_.P2M_UpperTheory_Reformulated_B_CardEmbeddingsRestrict_card_embeddings_restrict__3e5c16d106ca τ
end GroundTheory.Heights₂.Heights
