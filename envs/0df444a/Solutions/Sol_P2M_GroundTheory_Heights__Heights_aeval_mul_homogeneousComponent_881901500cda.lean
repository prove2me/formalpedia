-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_aeval_mul_homogeneousComponent_881901500cda
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:25:37.738668+00:00
-- url     : https://prove2.me/submissions/232078e9-d8f4-448b-99a5-681a1b8111fe

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsFormsThroughPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsThroughPointIncIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsChartZeroTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsThroughTwoPointsTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsTrdegBaseAlgebraic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PComponentOfIncIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PFormsThroughPoint

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
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] {n : ℕ}
    (q : MvPolynomial (Fin n) F) (e : ℕ) (t : Ω) (x : Fin n → Ω) :
    aeval (fun m => t * x m) (homogeneousComponent e q) = t ^ e * aeval x (homogeneousComponent e q) := by
  rw [homogeneousComponent_apply, map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α hα => ?_
  rw [Finset.mem_filter] at hα
  simp only [aeval_monomial, Finsupp.prod, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  have hdeg : Finsupp.degree α = ∑ i ∈ α.support, α i := rfl
  rw [← hα.2, hdeg]
  ring
end GroundTheory.Heights₂.Heights
