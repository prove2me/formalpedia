-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AddBlockData_eval_Hom_monomial_blockVal_2e069a232866
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:34:31.356414+00:00
-- url     : https://prove2.me/submissions/9e8a5b2a-c79e-4334-87fe-8f2760d3f3cd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_ExtMapLiftOldOfIsWeightedHomogeneous

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
open GroundTheory.Heights₂.Heights.AddBlockData
variable {P : ArithVariety n} (D : AddBlockData P)
namespace GroundTheory.Heights₂.Heights.AddBlockData
theorem _root_.solution (d : Coord n →₀ ℕ) (r : ℤ) :
    eval₂Hom (Int.castRingHom (MvPolynomial (Option ι) P.FunField))
        (fun v : Coord n ↦ C (P.mkF (X v)) * X (some v.1)) (monomial d r) =
      C (P.mkF (monomial d r)) * ∏ k, X (some k) ^ (Finsupp.weight (coordDeg n) d k) := by
  rw [coe_eval₂Hom, eval₂_monomial, monomial_eq, Finsupp.prod_fintype _ _ (by simp),
    Finsupp.prod_fintype _ _ (by simp)]
  simp only [mul_pow, Finset.prod_mul_distrib, map_mul, map_prod, map_pow,
    weight_coordDeg_apply, Fintype.prod_sigma, Finset.prod_pow_eq_pow_sum]
  simp [mul_assoc]
end GroundTheory.Heights₂.Heights.AddBlockData
