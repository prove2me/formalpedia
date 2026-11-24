-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_RatioField_map_mem_8496003472e3
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:56:47.225858+00:00
-- url     : https://prove2.me/submissions/eadf564d-0013-4f35-b0cb-b73f7994e77d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StWWRatioBasis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsAlgebraicMapAdjoin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
variable {Ω Φ : Type*} [Field Ω] [Field Φ] [Algebra Ω Φ]
namespace GroundTheory.Heights₂.Heights.Inter
namespace RatioField
theorem _root_.solution [CharZero Ω] [CharZero Φ] {S : Set Ω} {L : IntermediateField ℚ Φ}
    (hS : ∀ w ∈ S, algebraMap Ω Φ w ∈ L) {z : Ω} (hz : z ∈ IntermediateField.adjoin ℚ S) :
    algebraMap Ω Φ z ∈ L := by
  have hle : (IntermediateField.adjoin ℚ S).map (algebraMap Ω Φ).toRatAlgHom ≤ L := by
    rw [IntermediateField.adjoin_map, IntermediateField.adjoin_le_iff]
    rintro _ ⟨w, hw, rfl⟩
    exact hS w hw
  exact hle ((IntermediateField.mem_map _).mpr ⟨z, hz, rfl⟩)
end RatioField
end GroundTheory.Heights₂.Heights.Inter
