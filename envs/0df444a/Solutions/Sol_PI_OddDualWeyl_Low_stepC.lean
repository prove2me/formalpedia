-- Prove2me | solution 1 for PI.OddDualWeyl.Low.stepC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:25:13.686535+00:00
-- url     : https://prove2.me/submissions/5d3ed50a-14f0-4cb0-adc1-5220e422f274

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_MnrUpdateEqZero
import Theorems.Thm_PI_OddDualWeyl_Low_pMinor_eq
import Theorems.Thm_PI_OddDualWeyl_Low_rowGen_mnr_of_eq
import Theorems.Thm_PI_OddDualWeyl_Low_mnr_update_eq_zero
import Theorems.Thm_PI_OddDualWeyl_Low_mnr_comp_swap

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
theorem _root_.solution (s : Fin (n + 1)) (hs : i.val < s.val) :
    rowGen R (σ i.succ) (σ i.castSucc) (pMinor R σ (s.val + 1) s.isLt) =
      Polynomial.C (pMinor R σ (s.val + 1) s.isLt) ∧
    pMinor R (σ * Equiv.swap i.castSucc i.succ) (s.val + 1) s.isLt = - pMinor R σ (s.val + 1) s.isLt := by
  classical
  set p0 : Fin (s.val + 1) := ⟨i.val, by omega⟩ with hp0
  set p1 : Fin (s.val + 1) := ⟨i.val + 1, by omega⟩ with hp1
  have h0 : Fin.castLE s.isLt p0 = i.castSucc := Fin.ext (by simp [hp0])
  have h1 : Fin.castLE s.isLt p1 = i.succ := Fin.ext (by simp [hp1])
  have hne : p1 ≠ p0 := by intro e; have := congrArg Fin.val e; simp [hp0, hp1] at this
  constructor
  · rw [pMinor_eq, rowGen_mnr_of_eq _ _ _ _ (σ.injective.comp (Fin.castLE_injective _)) p0
      (by simp only [Function.comp, h0]), mnr_update_eq_zero _ _ _ p0 p1 hne
      (by simp only [Function.comp, h1])]
    simp
  · have key : (σ * Equiv.swap i.castSucc i.succ) ∘ Fin.castLE s.isLt =
        (σ ∘ Fin.castLE s.isLt) ∘ Equiv.swap p0 p1 := by
      funext p
      simp only [Function.comp, Equiv.Perm.mul_apply]
      congr 1
      rw [← h0, ← h1, (Fin.castLE_injective s.isLt).swap_apply]
    rw [pMinor_eq, pMinor_eq, key, mnr_comp_swap _ _ _ _ hne.symm]
end PI.OddDualWeyl.Low
