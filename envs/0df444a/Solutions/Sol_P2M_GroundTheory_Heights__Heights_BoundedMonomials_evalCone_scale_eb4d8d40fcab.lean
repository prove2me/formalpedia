-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_BoundedMonomials_evalCone_scale_eb4d8d40fcab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:40:40.835189+00:00
-- url     : https://prove2.me/submissions/982f0bb0-cf1d-4435-bae6-abc4751fb1d2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_EvalConeChartMonomialNeZero
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_BoundedMonomials_prod_pow_weight_36e2650dc969

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
open MvPolynomial
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
open GroundTheory.Heights₂.Heights.BoundedMonomials
namespace GroundTheory.Heights₂.Heights.BoundedMonomials
theorem _root_.solution {F : Type*} [CommRing F] (u : ι → F) (z : Cone n F)
    {f : MvPolynomial (Coord n) ℤ} {δ : ι → ℕ} (hf : IsWeightedHomogeneous (coordDeg n) f δ) :
    evalCone (fun k i ↦ u k * z k i) f = (∏ k, u k ^ δ k) * evalCone z f := by
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  simp only [evalCone, eval₂_sum, eval₂_monomial, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  have hw : Finsupp.weight (coordDeg n) m = δ := hf (mem_support_iff.mp hm)
  rw [← hw, ← prod_pow_weight u m]
  simp only [mul_pow, Finsupp.prod_mul]
  ring
end GroundTheory.Heights₂.Heights.BoundedMonomials
