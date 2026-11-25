-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolyLine_fwdDiff_iter_poly_f9e7acfe1226
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:55:24.747845+00:00
-- url     : https://prove2.me/submissions/ede2ff1e-8d85-4352-a002-06b444b692dc

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
theorem _root_.solution (D : ℕ) (P : ℚ[X]) (hP : P.natDegree ≤ D) :
    (fwdDiff (1 : ℚ))^[D] P.eval 0 = (D.factorial : ℚ) * P.coeff D := by
  rcases hP.lt_or_eq with h | h
  · rw [Polynomial.fwdDiff_iter_eq_zero_of_degree_lt h, coeff_eq_zero_of_natDegree_lt h]
    simp
  · subst h
    rw [Polynomial.fwdDiff_iter_degree_eq_factorial]
    rw [Polynomial.coeff_natDegree]
    simp only [Pi.smul_apply, Pi.natCast_apply, smul_eq_mul]
    ring
end GroundTheory.Heights₂.Heights.HilbertSamuel.EventualPolyLine
