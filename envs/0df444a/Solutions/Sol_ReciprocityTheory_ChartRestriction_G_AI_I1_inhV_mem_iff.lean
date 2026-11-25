-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.I1.inhV_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:33:59.503018+00:00
-- url     : https://prove2.me/submissions/45bc2125-fd7f-48ef-9b4f-df8755d509f4

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
theorem _root_.solution (f : MvPolynomial σ F) : f ∈ inhV F S ↔ inhKill F S f = 0 := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have : inhKill F S f = inhQuotEquiv F S (Ideal.Quotient.mk _ f) := rfl
  rw [this, map_eq_zero_iff _ (inhQuotEquiv F S).injective]
end ReciprocityTheory.ChartRestriction.G.AI.I1
