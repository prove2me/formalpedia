-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_RatioField_isAlgebraic_map_adjoin_2b59eaf5fe04
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:53:08.366257+00:00
-- url     : https://prove2.me/submissions/ea945038-de2a-4b9e-b211-064526ce2bd2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StWWRatioBasis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsAlgebraicMapAdjoin
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_RatioField_map_mem_8496003472e3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_RatioField_isAlgebraic_map_f9ef88b8fca0

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
theorem _root_.solution [CharZero Ω] [CharZero Φ] {d : ℕ} {t : Fin d → Ω}
    (ht : AlgebraicIndependent ℚ t) {S : Set Ω}
    (hS : ∀ w ∈ S, IsAlgebraic (IntermediateField.adjoin ℚ (Set.range t)) w) {s : Set Φ}
    (hs : ∀ n, algebraMap Ω Φ (t n) ∈ s) {z : Ω} (hz : z ∈ IntermediateField.adjoin ℚ S) :
    IsAlgebraic (IntermediateField.adjoin ℚ s) (algebraMap Ω Φ z) := by
  have h := RatioField.map_mem (L := (algebraicClosure (IntermediateField.adjoin ℚ s) Φ).restrictScalars ℚ)
    (fun w hw => (IntermediateField.mem_restrictScalars ℚ).mpr
      (mem_algebraicClosure_iff.mpr (RatioField.isAlgebraic_map ht (hS w hw) hs))) hz
  exact mem_algebraicClosure_iff.mp ((IntermediateField.mem_restrictScalars ℚ).mp h)
end RatioField
end GroundTheory.Heights₂.Heights.Inter
