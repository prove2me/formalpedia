-- Prove2me | solution 1 for PI.OddDualWeyl.Misc.sgn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:58:55.567229+00:00
-- url     : https://prove2.me/submissions/f507796b-e563-4fe9-8a4b-990861015fa9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_ExistsEqMulOfColumnSpanLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
noncomputable section
open PI PI.OddDualWeyl
open PI.OddDualWeyl.Misc
namespace PI.OddDualWeyl.Misc
theorem _root_.solution (K : Type) [Field K] (m : ℕ) : sgnK K m = 1 ∨ sgnK K m = -1 := by
  have h : PI.OddDualWeyl.sgnK K m =
      ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (m + 1))) : ℤ) : K) := by
    unfold PI.OddDualWeyl.sgnK PI.OddDualWeyl.revCol
    have hr : (Fin.rev : Fin (m + 1) → Fin (m + 1)) = ⇑(Fin.revPerm : Equiv.Perm (Fin (m + 1))) := rfl
    rw [hr, Matrix.det_permute', Matrix.det_one, mul_one]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (m + 1)))) with hs | hs <;>
    simp [h, hs]
end PI.OddDualWeyl.Misc
