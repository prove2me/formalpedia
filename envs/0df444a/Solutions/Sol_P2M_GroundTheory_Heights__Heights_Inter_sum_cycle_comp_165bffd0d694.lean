-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_sum_cycle_comp_165bffd0d694
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:00:16.935189+00:00
-- url     : https://prove2.me/submissions/1cff9ef4-f27d-47e3-a1ca-1161895cebf0

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
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution {α : Type*} (F : α →₀ ℕ) (G : α → α →₀ ℕ) (c : α → ℝ) :
    (F.sum fun W m => (m : ℝ) * (G W).sum fun U k => (k : ℝ) * c U) =
      (F.sum fun W m => m • G W).sum fun U k => (k : ℝ) * c U := by
  rw [Finsupp.sum_sum_index (fun _ => by simp) (fun _ _ _ => by push_cast; ring)]
  refine Finsupp.sum_congr fun W _ => ?_
  rw [Finsupp.sum_smul_index' (fun _ => by simp), Finsupp.mul_sum]
  refine Finsupp.sum_congr fun U _ => ?_
  simp only [smul_eq_mul, Nat.cast_mul]
  ring
end GroundTheory.Heights₂.Heights.Inter
