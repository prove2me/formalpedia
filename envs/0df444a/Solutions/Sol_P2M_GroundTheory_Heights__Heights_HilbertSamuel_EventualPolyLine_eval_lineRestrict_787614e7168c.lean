-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolyLine_eval_lineRestrict_787614e7168c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:55:21.500281+00:00
-- url     : https://prove2.me/submissions/07f85d3b-87af-4d7a-93a2-9fcc380014a0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsEventualPolyLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PEventualValueFacts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PEventualPolyLine

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open Polynomial GroundTheory.Heights₂.Heights.NumbersDVR fwdDiff
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.EventualPolyLine
variable {K : Type}
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.EventualPolyLine
theorem _root_.solution [Fintype K] (a c : K → ℚ) (p : MvPolynomial K ℚ) (t : ℚ) :
    (lineRestrict a c p).eval t = MvPolynomial.eval (fun k => c k + t * a k) p := by
  unfold lineRestrict
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp only [map_add, Polynomial.eval_add, hp, hq]
  | mul_X p k hp =>
    simp only [map_mul, Polynomial.eval_mul, hp, MvPolynomial.aeval_X, MvPolynomial.eval_X,
      Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X]
    ring
end GroundTheory.Heights₂.Heights.HilbertSamuel.EventualPolyLine
