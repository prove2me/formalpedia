-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.I1.inhV_dim
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:53.259797+00:00
-- url     : https://prove2.me/submissions/ea8d745a-2e97-41ca-aba8-212f4b8b33eb

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
theorem _root_.solution [Finite σ] :
    ringKrullDim (MvPolynomial σ F ⧸ inhV F S) = (Nat.card {s // s ∉ S} : WithBot ℕ∞) := by
  rw [ringKrullDim_eq_of_ringEquiv (inhQuotEquiv F S).toRingEquiv,
    MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add]
end ReciprocityTheory.ChartRestriction.G.AI.I1
