-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmBorderFull.Four.qminor_bE_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:41:44.45192+00:00
-- url     : https://prove2.me/submissions/b327c1f8-5958-44cb-9454-35811a16e859

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BorderMinorRotation_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BorderMinorRotation_SkipTwoSuccAboveComp
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderFull_Four_cons_comp_finRotate
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderFull_Four_neg_one_pow_mul_self
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset Formalism.REAL
noncomputable section
namespace PI.UnitaryGroupMassFormula.QmBorderFull.Four
open PI
private theorem qminor_comp_perm_eq_sign_mul {A : Type} [Ring A] [Algebra ℂ A] {n t : ℕ}
    (E : Fin n → Fin n → A) (a b : Fin t → Fin n) (τ : Equiv.Perm (Fin t)) (u : ℂ) :
    qminor E (a ∘ τ) b u = ((Equiv.Perm.sign τ : ℤ) : A) * qminor E a b u := by
  unfold qminor
  rw [Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft τ) _ _ fun σ => ?_
  simp only [Function.comp_apply, Equiv.coe_mulLeft, Equiv.Perm.coe_mul, Equiv.Perm.sign_mul]
  rw [← mul_assoc]
  congr 1
  rw [Units.val_mul, Int.cast_mul, ← mul_assoc, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self,
    Units.val_one, Int.cast_one, one_mul]
end PI.UnitaryGroupMassFormula.QmBorderFull.Four
end
end

set_option autoImplicit false
open Finset Formalism.REAL
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.QmBorderFull PI.UnitaryGroupMassFormula.QmBorderFull.Four
open PI
namespace PI.UnitaryGroupMassFormula.QmBorderFull.Four
theorem _root_.solution {A : Type} [Ring A] [Algebra ℂ A] {n t : ℕ} (E : Fin n → Fin n → A) (e : Fin n)
    (f : Fin t → Fin n) (b : Fin (t + 1) → Fin n) (u : ℂ) :
    qminor E (bE e f) b u = (((-1 : ℤ) ^ t : ℤ) : A) * qminor E (bS f e) b u := by
  have h := qminor_comp_perm_eq_sign_mul E (bE e f) b (finRotate (t + 1)) u
  rw [cons_comp_finRotate, sign_finRotate, Nat.add_sub_cancel] at h
  rw [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one] at h
  rw [h, ← mul_assoc, ← Int.cast_mul, neg_one_pow_mul_self, Int.cast_one, one_mul]
end PI.UnitaryGroupMassFormula.QmBorderFull.Four
