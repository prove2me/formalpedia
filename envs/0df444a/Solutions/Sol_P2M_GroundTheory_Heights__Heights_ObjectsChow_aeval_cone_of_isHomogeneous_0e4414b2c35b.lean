-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ObjectsChow_aeval_cone_of_isHomogeneous_0e4414b2c35b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:45:12.197801+00:00
-- url     : https://prove2.me/submissions/6ff344a6-c515-4fad-89ae-1d23d329d397

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsClosedPointConeCoord
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PClosedPointConeCoord

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
open GroundTheory.Heights₂.Heights.ObjectsChow
open MvPolynomial
namespace GroundTheory.Heights₂.Heights.ObjectsChow
theorem _root_.solution {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] {n d : ℕ}
    (y : Fin n → Ω) {p : MvPolynomial (Fin n) F} (hp : p.IsHomogeneous d) :
    aeval (fun j => Polynomial.C (y j) * Polynomial.X) p =
      Polynomial.C (aeval y p) * Polynomial.X ^ d := by
  classical
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  rw [map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg : ∑ j ∈ m.support, m j = d := by
    have := hp (mem_support_iff.mp hm)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  rw [aeval_monomial, aeval_monomial, Finsupp.prod, Finsupp.prod]
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg, ← map_pow,
    ← map_prod, Polynomial.algebraMap_apply, map_mul, mul_assoc]
end GroundTheory.Heights₂.Heights.ObjectsChow
