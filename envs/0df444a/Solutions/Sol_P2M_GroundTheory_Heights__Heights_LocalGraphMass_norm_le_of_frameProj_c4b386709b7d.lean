-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LocalGraphMass_norm_le_of_frameProj_c4b386709b7d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:02:59.484907+00:00
-- url     : https://prove2.me/submissions/e73f7529-798d-4a8a-9d95-3ac50b5540bb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalGraphMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLocalGraphMass

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Function
open scoped ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.LocalGraphMass
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.LocalGraphMass
theorem _root_.solution (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (I : Finset (Fin n)) (z : EuclideanSpace ℂ (Fin n)) (x : EuclideanSpace ℂ I)
    (hx : WithLp.ofLp x = frameProj b I z) : ‖x‖ ≤ ‖z‖ := by
  have h1 : ‖x‖ ^ 2 = ∑ i ∈ I, ‖inner ℂ (b i) z‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, ← Finset.sum_coe_sort I]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := congrFun hx i
    simp only [frameProj] at this
    simp [this]
  have h2 := b.orthonormal.sum_inner_products_le (s := I) (x := z)
  nlinarith [norm_nonneg x, norm_nonneg z]
end GroundTheory.Heights₂.Heights.LocalGraphMass
