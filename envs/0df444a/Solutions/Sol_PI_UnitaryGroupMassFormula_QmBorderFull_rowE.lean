-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmBorderFull.rowE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:50:02.423549+00:00
-- url     : https://prove2.me/submissions/44f17f67-f6cc-4ce9-9eb9-96b9de863020

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BorderMinorRotation_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BorderMinorRotation_SkipOneEqSuccAbove
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderFull_rot_cons

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Formalism.REAL
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.QmBorderFull
open PI
namespace PI.UnitaryGroupMassFormula.QmBorderFull
theorem _root_.solution (hLR : ExpLastRow) {A : Type} [Ring A] [Algebra ℂ A] {n k : ℕ} (E : Fin n → Fin n → A)
    (hE : GlRel E) (e : Fin n) (W : Fin k → Fin n) (v : Fin (k + 1) → Fin n) (he : ∀ x, v x ≠ e) (u : ℂ) :
    qminor E (bE e W) v u =
      ∑ x : Fin (k + 1), (((-1 : ℤ) ^ (x : ℕ) : ℤ) : A) * (qminor E W (v ∘ x.succAbove) (u - 1) * E e (v x)) := by
  have hperm : ∀ (a : Fin (k + 1) → Fin n) (τ : Equiv.Perm (Fin (k + 1))),
      qminor E (a ∘ τ) v u = ((Equiv.Perm.sign τ : ℤ) : A) * qminor E a v u := by
    intro a τ
    unfold qminor
    rw [Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft τ) _ _ (fun σ => ?_)
    have hτ : ((Equiv.Perm.sign τ : ℤ) : A) * ((Equiv.Perm.sign τ : ℤ) : A) = 1 := by
      rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
    simp only [Equiv.coe_mulLeft, Equiv.Perm.mul_apply, Function.comp_apply, Equiv.Perm.sign_mul,
      Units.val_mul, Int.cast_mul]
    rw [← mul_assoc, ← mul_assoc, hτ, one_mul]
  have hs : ∀ x : Fin (k + 1), ((Equiv.Perm.sign (finRotate (k + 1)).symm : ℤ) : A) *
      (((-1 : ℤ) ^ (k + (x : ℕ)) : ℤ) : A) = (((-1 : ℤ) ^ (x : ℕ) : ℤ) : A) := by
    intro x
    rw [Equiv.Perm.sign_symm, sign_finRotate, ← Int.cast_mul, Units.val_pow_eq_pow_val, Units.val_neg,
      Units.val_one, ← pow_add]
    congr 1
    have hx : ∀ a : ℕ, a = 2 * k + (x : ℕ) → (-1 : ℤ) ^ a = (-1) ^ (x : ℕ) := by
      rintro a rfl
      rw [pow_add, pow_mul, neg_one_sq, one_pow, one_mul]
    exact hx _ (by omega)
  rw [rot_cons e W, hperm, hLR A n k E hE (Fin.snoc (α := fun _ => Fin n) W e) v u, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  have h1 : (Fin.snoc (α := fun _ => Fin n) W e ∘ Fin.castSucc) = W := by
    funext i
    simp
  have h2 : Tm E u e (v x) = E e (v x) := by
    unfold Tm
    rw [if_neg (fun h => he x h.symm), zero_add]
  rw [← mul_assoc, hs x, h1, Fin.snoc_last, h2]
end PI.UnitaryGroupMassFormula.QmBorderFull
