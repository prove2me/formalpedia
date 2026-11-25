-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_ChartDetRatio_mem_adjoin_of_mem_chartRing_d26bab57a1af
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:13:56.713834+00:00
-- url     : https://prove2.me/submissions/e81e3ec7-f2ee-4c94-b00d-615d5249f6a6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StChartDetRatio
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PChartDetRatio

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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
namespace GroundTheory.Heights₂.Heights.Inter
namespace ChartDetRatio
theorem _root_.solution {Ω : Type} [Field Ω] [CharZero Ω] {ι : Type} (x : ι → Ω)
    (i₀ : ι) {a : Ω} (ha : a ∈ chartRing ℤ x i₀) :
    a ∈ IntermediateField.adjoin ℚ (Set.range fun j => x j / x i₀) := by
  induction ha using Algebra.adjoin_induction with
  | mem y hy => exact IntermediateField.subset_adjoin ℚ _ hy
  | algebraMap r =>
    rw [eq_intCast]
    exact intCast_mem _ r
  | add y z _ _ hy hz => exact add_mem hy hz
  | mul y z _ _ hy hz => exact mul_mem hy hz
end ChartDetRatio
end GroundTheory.Heights₂.Heights.Inter
