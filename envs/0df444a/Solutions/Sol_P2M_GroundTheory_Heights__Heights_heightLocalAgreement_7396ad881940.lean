-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_heightLocalAgreement_7396ad881940
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:40:48.092662+00:00
-- url     : https://prove2.me/submissions/6678a264-cd35-4c71-a6d5-7faeecb1d719

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CardEmbeddingsRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FieldChange
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_height_eq_of_le_ddd9ed9a76c6

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
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution : HeightLocalAgreement.Statement := by
  intro ι ι' _ _ _ _ n n' A A' x x' hx0 hx0' L _ hx hx' hfin harch
  rw [height_eq_of_le A hx0 L hx, height_eq_of_le A' hx0' L hx', finsum_congr hfin,
    Finset.sum_congr rfl fun σ _ ↦ by rw [harch σ]]
end GroundTheory.Heights₂.Heights
