-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.H1.IntegralRingEmbedding.val_pos_of_mem_max
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:07:41.193804+00:00
-- url     : https://prove2.me/submissions/f9a4c927-7ba6-4111-a7cb-01c6ac7f6e35

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_NakayamaChar
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_IntegralRingEmbedding
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_IntegralRingEmbedding_mem_intRing
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_IntegralRingEmbedding_isUnit_of_val_zero

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
theorem _root_.solution (x : intRing v) (hx : x ∈ IsLocalRing.maximalIdeal (intRing v)) :
    0 < v (x : F) := by
  have hnu : ¬ IsUnit x := (IsLocalRing.mem_maximalIdeal x).1 hx
  have h0 : 0 ≤ v (x : F) := (mem_intRing v).1 x.2
  exact lt_of_le_of_ne h0 (fun h => hnu (isUnit_of_val_zero v x h.symm))
end ReciprocityTheory.ChartRestriction.G.H1.IntegralRingEmbedding
