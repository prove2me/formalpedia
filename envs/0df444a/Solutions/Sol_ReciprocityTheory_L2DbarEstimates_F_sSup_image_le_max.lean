-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.sSup_image_le_max
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:17:59.893929+00:00
-- url     : https://prove2.me/submissions/9ec35421-937f-4a10-a1fd-dd4a45d1cf80

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_Choice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.F
theorem _root_.solution {M : Type*} (g : M → ℝ) (s : Set M) (B : ℝ)
    (hB : ∀ x ∈ s, g x ≤ B) : sSup (g '' s) ≤ max B 0 := by
  refine Real.sSup_le ?_ (le_max_right _ _)
  rintro _ ⟨x, hx, rfl⟩
  exact (hB x hx).trans (le_max_left _ _)
end ReciprocityTheory.L2DbarEstimates.F
