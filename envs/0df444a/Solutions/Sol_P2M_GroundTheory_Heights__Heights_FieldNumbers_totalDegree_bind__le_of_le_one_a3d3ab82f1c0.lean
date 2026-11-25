-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_totalDegree_bind__le_of_le_one_a3d3ab82f1c0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:54:13.000309+00:00
-- url     : https://prove2.me/submissions/4c9fc0c8-6b35-4fcd-80ce-4265e9d4931f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegreeBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PEventuallyPolyShift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial Filter
noncomputable section
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution {σ τ R : Type*} [CommSemiring R]
    (f : σ → MvPolynomial τ R) (hf : ∀ i, (f i).totalDegree ≤ 1) (p : MvPolynomial σ R) :
    (bind₁ f p).totalDegree ≤ p.totalDegree := by
  conv_lhs => rw [p.as_sum, map_sum]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun s hs => ?_)
  rw [bind₁_monomial]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  refine le_trans ?_ (le_totalDegree hs)
  refine Finset.sum_le_sum fun i _ => ?_
  refine (totalDegree_pow _ _).trans ?_
  simpa using Nat.mul_le_mul_left (s i) (hf i)
end GroundTheory.Heights₂.Heights.FieldNumbers
