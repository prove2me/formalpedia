-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ThroughPointIncIdeal_eval_genSubst_vanish_909cfb66c306
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:22:28.971986+00:00
-- url     : https://prove2.me/submissions/5a9b5f73-bf48-432f-b24b-d0caded01a37

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsThroughPointIncIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PThroughPointIncIdeal

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
namespace GroundTheory.Heights₂.Heights
namespace ThroughPointIncIdeal
theorem _root_.solution {K : Type*} [Field K] {n k : ℕ} (x c : Fin n → K)
    (hc : ∑ j, c j * x j = 1) (a : Fin k × Fin n → K) (i : Fin k) :
    ∑ j, eval a (genSubst (k := k) x c (i, j)) * x j = 0 := by
  have h : ∀ j, eval a (genSubst (k := k) x c (i, j)) =
      a (i, j) - (∑ l, a (i, l) * x l) * c j := fun j => by simp [genSubst]
  simp_rw [h, sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum, hc, mul_one, sub_self]
end ThroughPointIncIdeal
end GroundTheory.Heights₂.Heights
