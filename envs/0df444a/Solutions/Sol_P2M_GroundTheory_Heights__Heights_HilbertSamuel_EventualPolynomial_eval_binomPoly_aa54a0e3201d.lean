-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolynomial_eval_binomPoly_aa54a0e3201d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:55:21.787929+00:00
-- url     : https://prove2.me/submissions/4d11c4d0-d160-4e58-8b0d-5497b2033e32

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsEventualPolynomial
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PEventualPolynomial

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
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR Finset fwdDiff
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.EventualPolynomial
variable {K : Type} [DecidableEq K]
omit [DecidableEq K]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.EventualPolynomial
theorem _root_.solution (c : ℕ) (k : K) (j : ℕ) (x : K → ℚ) (m : ℕ) (hx : x k = (m : ℚ) + c) :
    eval x (binomPoly c k j) = (m.choose j : ℚ) := by
  unfold binomPoly
  simp only [map_mul, eval_C, map_prod, map_sub, eval_X, hx]
  have : ∏ i ∈ range j, ((m : ℚ) + c - ((c + i : ℕ) : ℚ)) = ∏ i ∈ range j, ((m : ℚ) - i) :=
    prod_congr rfl fun i _ => by push_cast; ring
  rw [this, ← descPochhammer_eval_eq_prod_range, descPochhammer_eval_eq_descFactorial,
    Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul, ← mul_assoc,
    inv_mul_cancel₀ (by positivity), one_mul]
end GroundTheory.Heights₂.Heights.HilbertSamuel.EventualPolynomial
