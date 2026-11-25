-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_exists_embedding_over_b3860a0a3dd0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:45:48.240968+00:00
-- url     : https://prove2.me/submissions/16956810-9c51-4fef-90d9-65961f6456ce

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_QuadraticConj
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_CMDatum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open NumberField GroundTheory.Automorphic
variable (F E : Type*) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E]
  [IsTotallyComplex E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {F E}
variable (F E)
variable {F E}
variable (F E)
namespace GroundTheory.Heights₂.Theta
theorem _root_.solution (v : InfinitePlace F) :
    ∃ φ : E →+* ℂ, InfinitePlace.mk (φ.comp (algebraMap F E)) = v := by
  obtain ⟨w, hw⟩ := InfinitePlace.comap_surjective (k := F) (K := E) v
  refine ⟨w.embedding, ?_⟩
  rw [← InfinitePlace.comap_mk, InfinitePlace.mk_embedding]
  exact hw
end GroundTheory.Heights₂.Theta
