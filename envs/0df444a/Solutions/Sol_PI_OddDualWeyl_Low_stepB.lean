-- Prove2me | solution 1 for PI.OddDualWeyl.Low.stepB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:31:31.97043+00:00
-- url     : https://prove2.me/submissions/c5151600-9f3b-4259-9393-69e8194d1cc6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_MnrUpdateEqZero
import Theorems.Thm_PI_OddDualWeyl_Low_pMinor_eq
import Theorems.Thm_PI_OddDualWeyl_Low_rowGen_mnr_of_eq
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
theorem _root_.solution (s : Fin (n + 1)) (hs : s.val = i.val) :
    rowGen R (σ i.succ) (σ i.castSucc) (pMinor R σ (s.val + 1) s.isLt) =
      Polynomial.C (pMinor R σ (s.val + 1) s.isLt) +
      Polynomial.X * Polynomial.C (pMinor R (σ * Equiv.swap i.castSucc i.succ) (s.val + 1) s.isLt) := by
  classical
  have hl : Fin.castLE s.isLt (Fin.last s.val) = i.castSucc := Fin.ext (by simp [hs])
  have key : (σ * Equiv.swap i.castSucc i.succ) ∘ Fin.castLE s.isLt =
      Function.update (σ ∘ Fin.castLE s.isLt) (Fin.last s.val) (σ i.succ) := by
    funext p
    by_cases hp : p = Fin.last s.val
    · subst hp
      simp only [Function.comp, Equiv.Perm.mul_apply, Function.update_self, hl, Equiv.swap_apply_left]
    · have hlt := Fin.val_lt_last hp
      rw [Function.update_of_ne hp]
      simp only [Function.comp, Equiv.Perm.mul_apply]
      rw [Equiv.swap_apply_of_ne_of_ne (castLE_ne_of_lt _ p _ (by simp; omega))
        (castLE_ne_of_lt _ p _ (by simp; omega))]
  rw [pMinor_eq, pMinor_eq, key]
  exact rowGen_mnr_of_eq _ _ _ _ (σ.injective.comp (Fin.castLE_injective _)) _
    (by simp only [Function.comp, hl])
end PI.OddDualWeyl.Low
