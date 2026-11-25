-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ObjectsChow_aeval_smul_of_isHomogeneous_01baa75c08b8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:52:25.299322+00:00
-- url     : https://prove2.me/submissions/7a5ef444-fdd3-48f0-b000-3880596cc847

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsClosedPointChartField
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsClosedPointConeCoord
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PIntChowFormExists
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PChowFormHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PNormFormIrreducible
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PChowDegreeClosedPoint
import Theorems.Thm_GroundTheory_Arith_Toric_LowerBound_sum


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
open MvPolynomial Vertical Vertical.NormFormIrreducible
namespace GroundTheory.Heights₂.Heights.ObjectsChow
theorem _root_.solution {F K : Type*} [Field F] [Field K] [Algebra F K] {n d : ℕ}
    {g : MvPolynomial (Fin n) F} (hg : g.IsHomogeneous d) (c : K) (y : Fin n → K) :
    aeval (fun j => c * y j) g = c ^ d * aeval y g := by
  classical
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg : ∑ j ∈ m.support, m j = d := by
    have := hg (mem_support_iff.mp hm)
    rw [Finsupp.weight_apply, Finsupp.sum] at this
    simpa using this
  rw [aeval_monomial, aeval_monomial]
  simp only [mul_pow]
  rw [Finsupp.prod_mul, Finsupp.prod, Finset.prod_pow_eq_pow_sum, hdeg]
  ring
end GroundTheory.Heights₂.Heights.ObjectsChow
