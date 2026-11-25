-- Prove2me | solution 1 for PI.OddDualWeyl.Low.stepA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:16:13.037827+00:00
-- url     : https://prove2.me/submissions/a2060984-425d-4f73-9bfe-2b2ed9dfc454

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_MnrUpdateEqZero
import Theorems.Thm_PI_OddDualWeyl_Low_pMinor_eq
import Theorems.Thm_PI_OddDualWeyl_Low_rowGen_mnr_of_not
import Theorems.Thm_PI_OddDualWeyl_Low_castLE_ne_of_lt

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
open PI PI.OddDualWeyl PI.OddDualWeyl.Low
variable {R : Type*} [CommRing R]
variable {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) (i : Fin n)
namespace PI.OddDualWeyl.Low
theorem _root_.solution (s : Fin (n + 1)) (hs : s.val < i.val) :
    rowGen R (σ i.succ) (σ i.castSucc) (pMinor R σ (s.val + 1) s.isLt) =
      Polynomial.C (pMinor R σ (s.val + 1) s.isLt) ∧
    pMinor R (σ * Equiv.swap i.castSucc i.succ) (s.val + 1) s.isLt = pMinor R σ (s.val + 1) s.isLt := by
  constructor
  · rw [pMinor_eq]
    apply rowGen_mnr_of_not
    intro p hp
    exact castLE_ne_of_lt _ p _ (by simp; omega) (σ.injective hp)
  · rw [pMinor_eq, pMinor_eq]
    congr 1
    funext p
    simp only [Function.comp, Equiv.Perm.mul_apply]
    rw [Equiv.swap_apply_of_ne_of_ne (castLE_ne_of_lt _ p _ (by simp; omega))
      (castLE_ne_of_lt _ p _ (by simp; omega))]
end PI.OddDualWeyl.Low
