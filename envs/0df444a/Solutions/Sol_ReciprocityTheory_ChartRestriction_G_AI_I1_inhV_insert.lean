-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.I1.inhV_insert
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:27:11.535117+00:00
-- url     : https://prove2.me/submissions/33c459ad-3819-4dfb-bd4b-6c0133bbfd13

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_InhDivCycleOfSuppEmpty

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
theorem _root_.solution (p : σ) : inhV F S ⊔ Ideal.span {X p} = inhV F (insert p S) := by
  simp only [inhV, Finset.coe_insert, Set.image_insert_eq, Ideal.span_insert]
  exact sup_comm _ _
end ReciprocityTheory.ChartRestriction.G.AI.I1
