-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.I1.inhV_X_nmem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:41:19.078638+00:00
-- url     : https://prove2.me/submissions/83704505-4bc9-4ad6-b1ff-e6522f718c6d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_InhDivCycleOfSuppEmpty
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_inhV_mem_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {σ : Type*} (F : Type*) [Field F] [DecidableEq σ] (S : Finset σ)
namespace ReciprocityTheory.ChartRestriction.G.AI.I1
theorem _root_.solution {s : σ} (h : s ∉ S) : (X s : MvPolynomial σ F) ∉ inhV F S := by
  rw [inhV_mem_iff, inhKill_X_nmem F S h]
  exact X_ne_zero _
end ReciprocityTheory.ChartRestriction.G.AI.I1
