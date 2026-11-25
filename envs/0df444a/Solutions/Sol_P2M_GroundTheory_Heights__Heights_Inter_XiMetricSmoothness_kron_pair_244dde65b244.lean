-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_kron_pair_244dde65b244
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:07:42.951075+00:00
-- url     : https://prove2.me/submissions/671e6aec-b64e-44f4-91cc-3b064d0d9c73

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_XiPluckerCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PXiMetric

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
open MvPolynomial Matrix ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
open scoped ComplexOrder
set_option linter.unusedSectionVars false
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.XiMetricSmoothness
variable {κ : Type} [Fintype κ]
namespace GroundTheory.Heights₂.Heights.Inter.XiMetricSmoothness
theorem _root_.solution (G : Matrix κ κ ℂ) (a b c d : κ → ℂ) :
    star (fun p : κ × κ => a p.1 * b p.2) ⬝ᵥ (Matrix.kronecker G G *ᵥ fun p => c p.1 * d p.2) =
      hermG G a c * hermG G b d := by
  simp only [hermG, dotProduct, mulVec, Matrix.kronecker, kroneckerMap_apply, Pi.star_apply, star_mul',
    Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum]
  calc _ = ∑ m, ∑ k, ∑ k', ∑ m', star (a k) * star (b m) * (G k k' * G m m' * (c k' * d m')) :=
        Finset.sum_comm
    _ = ∑ m, ∑ m', ∑ k, ∑ k', star (a k) * star (b m) * (G k k' * G m m' * (c k' * d m')) := by
        refine Finset.sum_congr rfl fun m _ => ?_
        calc _ = ∑ k, ∑ m', ∑ k', star (a k) * star (b m) * (G k k' * G m m' * (c k' * d m')) :=
              Finset.sum_congr rfl fun k _ => Finset.sum_comm
          _ = _ := Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun m' _ =>
          Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun k' _ => ?_
        ring
end GroundTheory.Heights₂.Heights.Inter.XiMetricSmoothness
