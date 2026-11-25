-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_finsum_divSupp_eq_sum_14760c269bd2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:34:45.729843+00:00
-- url     : https://prove2.me/submissions/79c6f082-729a-42c6-b442-54047ed11008

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSwap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotLtLtOfMemMinimalPrimes
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_divCycle_apply_of_mem_738303062c77
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_divCycle_apply_of_not_mem_bf629faf9af2

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution (P : Ideal (MRing ι)) (s : MRing ι) (f : Ideal (MRing ι) → ℝ) :
    ∑ᶠ W ∈ divSupp P s, (multAt (P ⊔ Ideal.span {s}) W : ℝ) * f W =
      (divCycle P s).sum fun W m => (m : ℝ) * f W := by
  classical
  rw [finsum_mem_eq_finite_toFinset_sum _ (divSupp_finite P s), Finsupp.sum]
  have h1 : ∀ W ∈ (divSupp_finite P s).toFinset,
      (multAt (P ⊔ Ideal.span {s}) W : ℝ) * f W = (divCycle P s W : ℝ) * f W := by
    intro W hW
    rw [Set.Finite.mem_toFinset] at hW
    rw [divCycle_apply_of_mem hW]
  rw [Finset.sum_congr rfl h1]
  symm
  refine Finset.sum_subset (fun W hW => ?_) (fun W _ hW => ?_)
  · rw [Set.Finite.mem_toFinset]
    by_contra h
    exact (Finsupp.mem_support_iff.mp hW) (divCycle_apply_of_not_mem h)
  · rw [Finsupp.notMem_support_iff.mp hW]
    simp
end GroundTheory.Heights₂.Heights.Inter
