-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_sum_embeddings_restrict_5832e9921bd0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:33:57.549797+00:00
-- url     : https://prove2.me/submissions/77626149-28a3-4887-89c2-a56054be6264

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CardEmbeddingsRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FieldChange
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_card_embeddings_restrict_a19e8def3342

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
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (f : (K →+* ℂ) → ℝ) :
    ∑ σ : L →+* ℂ, f (σ.comp (algebraMap K L)) = finrank K L * ∑ τ : K →+* ℂ, f τ := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ (fun σ : L →+* ℂ ↦ σ.comp (algebraMap K L)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ ↦ ?_
  rw [Finset.sum_congr rfl (g := fun _ ↦ f τ) (fun σ hσ ↦ by rw [(Finset.mem_filter.mp hσ).2]),
    Finset.sum_const, card_embeddings_restrict, nsmul_eq_mul]
end GroundTheory.Heights₂.Heights
