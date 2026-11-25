-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PlaceCentredSum_centred_iff_dd0781008482
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:23:07.211502+00:00
-- url     : https://prove2.me/submissions/715f73ea-6221-441b-988c-3fbc33728b54

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightPlaceCentredSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PPlaceCentredSum
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PlaceCentredSum_apply_algebraMap_fc47d50d1873
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PlaceCentredSum_deg_ne_zero_16fd8e505679

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
open NumberField IsDedekindDomain Ideal
open GroundTheory.Heights₂.Heights.PlaceCentredSum
variable {L K : Type} [Field L] [NumberField L] [Field K] [NumberField K] [Algebra L K]
namespace GroundTheory.Heights₂.Heights.PlaceCentredSum
theorem _root_.solution (O : Subalgebra ℤ L) (m : Ideal O) (v : FinitePlace K) :
    AbsCentredAt O m (fun u ↦ v (algebraMap L K u)) ↔
      AbsCentredAt O m (fun u ↦ FinitePlace.mk (below v) u) := by
  have h1 : ∀ a : ℝ, 0 ≤ a → (a ^ deg L v ≤ 1 ↔ a ≤ 1) := fun a ha ↦
    pow_le_one_iff_of_nonneg ha (deg_ne_zero v)
  have h2 : ∀ a : ℝ, 0 ≤ a → (a ^ deg L v < 1 ↔ a < 1) := fun a ha ↦
    pow_lt_one_iff_of_nonneg ha (deg_ne_zero v)
  unfold AbsCentredAt
  simp only [apply_algebraMap]
  exact and_congr (forall_congr' fun u ↦ h1 _ (apply_nonneg _ _))
    (forall_congr' fun u ↦ by rw [h2 _ (apply_nonneg _ _)])
end GroundTheory.Heights₂.Heights.PlaceCentredSum
