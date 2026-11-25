-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.H1.IntegralRingEmbedding.wt_zero_of_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:07:45.191317+00:00
-- url     : https://prove2.me/submissions/95291bd8-3521-43d2-953d-6a85c6b210d1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_NakayamaChar
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_IntegralRingEmbedding

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.H1 ReciprocityTheory.ChartRestriction.G.H1.IntegralRingEmbedding
open Module
variable {F : Type} [Field F] (v : AddValuation F (WithTop ℚ))
namespace ReciprocityTheory.ChartRestriction.G.H1.IntegralRingEmbedding
theorem _root_.solution {a b : WithTop ℚ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a + b = 0) : a = 0 := by
  refine le_antisymm ?_ ha
  rw [← h]
  exact le_add_of_nonneg_right hb
end ReciprocityTheory.ChartRestriction.G.H1.IntegralRingEmbedding
