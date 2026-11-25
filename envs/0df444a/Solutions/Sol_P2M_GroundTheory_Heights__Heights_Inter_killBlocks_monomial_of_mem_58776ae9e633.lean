-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_killBlocks_monomial_of_mem_58776ae9e633
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:58:54.894708+00:00
-- url     : https://prove2.me/submissions/eb8d2e04-9f91-4c81-8c1f-a2d0dc6c0b30

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_RationalSections_ThmISt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_UniquenessDegreeFormOfIntersectionForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ArithVarZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
omit [Fintype K] [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution (S : Set K) (m : (Σ k, ι k) →₀ ℕ) (c : ℤ) (p : Σ k, ι k)
    (hp : p ∈ m.support) (hS : p.1 ∈ S) : killBlocks S (monomial m c : MRing ι) = 0 := by
  rw [killBlocks, aeval_monomial, Finsupp.prod]
  refine mul_eq_zero_of_right _ (Finset.prod_eq_zero hp ?_)
  rw [if_pos hS, zero_pow (Finsupp.mem_support_iff.mp hp)]
end GroundTheory.Heights₂.Heights.Inter
