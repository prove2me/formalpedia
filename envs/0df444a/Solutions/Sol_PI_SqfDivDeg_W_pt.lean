-- Prove2me | solution 1 for PI.SqfDivDeg.W.pt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:23:21.829315+00:00
-- url     : https://prove2.me/submissions/24118e2d-984a-4638-9cfa-6069f41762e2

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeDivisorDegree_MonicFintype
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeDivisorDegree_CardMonicTwoRootsLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Finset
noncomputable section
open PI PI.SqfDivDeg PI.SqfDivDeg.W
open Classical
namespace PI.SqfDivDeg.W
theorem _root_.solution (k : ℕ) : 2 * k ≤ (k * k - k) + 2 * (if k = 0 then 0 else 1) := by
  match k with
  | 0 => simp
  | 1 => simp
  | k + 2 =>
    have h : (k + 2) * (k + 2) - (k + 2) = (k + 2) * (k + 1) := by
      rw [Nat.sub_eq_iff_eq_add (by nlinarith)]
      ring
    rw [h]
    simp
    nlinarith
end PI.SqfDivDeg.W
