-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_eval_map_derivative_eq_sum_2fd815c9f283
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:25:29.967913+00:00
-- url     : https://prove2.me/submissions/e188680f-6c1c-42ad-b7dd-72cdabdad47b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ZeroLocusDimHGeo

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
open Metric Filter Topology Finset
noncomputable section
open GroundTheory.Heights₂.Heights.ZeroLocusDimH
namespace GroundTheory.Heights₂.Heights.ZeroLocusDimH
theorem _root_.solution {r : ℕ} (Q : Polynomial (MvPolynomial (Fin r) ℂ))
    (y : Fin r → ℂ) (t : ℂ) :
    Polynomial.eval t ((Polynomial.derivative Q).map (MvPolynomial.eval y)) =
      ∑ k ∈ range (Q.natDegree + 1), MvPolynomial.eval y (Q.coeff k) * ((k : ℂ) * t ^ (k - 1)) := by
  rw [← Polynomial.derivative_map, Polynomial.derivative_eval,
    Polynomial.sum_over_range' (n := Q.natDegree + 1) _ (fun _ => by simp)
      (lt_of_le_of_lt (Polynomial.natDegree_map_le) (Nat.lt_succ_self _))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Polynomial.coeff_map]
  ring
end GroundTheory.Heights₂.Heights.ZeroLocusDimH
