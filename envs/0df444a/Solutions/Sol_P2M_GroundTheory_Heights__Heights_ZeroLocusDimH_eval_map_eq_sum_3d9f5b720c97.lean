-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_eval_map_eq_sum_3d9f5b720c97
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:25:31.565389+00:00
-- url     : https://prove2.me/submissions/376084e3-9478-4edd-b72a-36a20d35bba8

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
theorem _root_.solution {r : ℕ} (Q : Polynomial (MvPolynomial (Fin r) ℂ)) (y : Fin r → ℂ) (t : ℂ) :
    Polynomial.eval t (Q.map (MvPolynomial.eval y)) =
      ∑ k ∈ range (Q.natDegree + 1), MvPolynomial.eval y (Q.coeff k) * t ^ k := by
  rw [Polynomial.eval_eq_sum_range' (n := Q.natDegree + 1)
    (lt_of_le_of_lt (Polynomial.natDegree_map_le) (Nat.lt_succ_self _))]
  simp [Polynomial.coeff_map]
end GroundTheory.Heights₂.Heights.ZeroLocusDimH
