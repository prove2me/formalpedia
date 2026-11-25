-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_finsum_hor_eq_c421a4deb190
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:58:41.710984+00:00
-- url     : https://prove2.me/submissions/613f945e-f40c-4e2c-9a96-46d57e5aeed0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSwap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotLtLtOfMemMinimalPrimes

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
open Classical
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution (P : Ideal (MRing ι)) (s : MRing ι) (g : Ideal (MRing ι) → ℝ) :
    (∑ᶠ (W) (_ : W ∈ divSupp P s ∧ IsHorizontal W), g W) =
      ∑ᶠ W ∈ divSupp P s, (if IsHorizontal W then g W else 0) := by
  classical
  rw [finsum_mem_eq_finite_toFinset_sum _ (divSupp_finite P s),
    finsum_cond_eq_sum_of_cond_iff g (t := (divSupp_finite P s).toFinset.filter IsHorizontal)
      (fun {x} _ => by simp), Finset.sum_filter]
end GroundTheory.Heights₂.Heights.Inter
