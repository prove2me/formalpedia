-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmMove.Nc_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:42:22.708425+00:00
-- url     : https://prove2.me/submissions/c23e8c83-ac6e-45d3-a4ec-5f67cf3ee8e4

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantVectorMove_SumPermEqSumFirstColumnSplit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantVectorMove_MoveOperatorCovariance
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmMove_extN_lt
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmMove_sgnlem
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
namespace PI.UnitaryGroupMassFormula.QmMove
section Cov
variable {A : Type*} [Ring A] [Algebra ℂ A] {n m : ℕ} (E : Fin n → Fin n → A) (η : Fin n → A)
  (a : Fin (m + 1) → Fin n) (b : Fin m → Fin n) (w : ℂ)
private lemma sum_perm_fin_succ_eq_sum_cycleRange_decomposeFin {M : Type*} [AddCommMonoid M] {k : ℕ} (π : Equiv.Perm (Fin (k + 1)))
    (F : Equiv.Perm (Fin (k + 1)) → M) :
    ∑ τ, F τ = ∑ j : Fin (k + 1), ∑ σ : Equiv.Perm (Fin k),
      F (j.cycleRange.symm * Equiv.Perm.decomposeFin.symm (0, σ) * π) := by
  have hb : Function.Bijective (fun x : Fin (k + 1) × Equiv.Perm (Fin k) =>
      x.1.cycleRange.symm * Equiv.Perm.decomposeFin.symm (0, x.2) * π) := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨?_, by simp [Fintype.card_perm, Nat.factorial_succ]⟩
    rintro ⟨j, σ⟩ ⟨j', σ'⟩ h
    have h1 : j.cycleRange.symm * Equiv.Perm.decomposeFin.symm (0, σ) =
        j'.cycleRange.symm * Equiv.Perm.decomposeFin.symm (0, σ') := mul_right_cancel h
    have hj : j = j' := by
      have := congrArg (fun e : Equiv.Perm (Fin (k + 1)) => e 0) h1
      simpa [Equiv.Perm.decomposeFin_symm_apply_zero, Fin.cycleRange_symm_zero] using this
    subst hj
    have h3 := (Equiv.injective Equiv.Perm.decomposeFin.symm) (mul_left_cancel h1)
    rw [show σ = σ' from congrArg Prod.snd h3]
  rw [← Fintype.sum_prod_type']
  exact (hb.sum_comp F).symm
end Cov
end PI.UnitaryGroupMassFormula.QmMove
end
end

set_option autoImplicit false
open Finset Formalism.REAL
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.QmMove
variable {A : Type*} [Ring A] [Algebra ℂ A] {n m : ℕ} (E : Fin n → Fin n → A) (η : Fin n → A)
  (a : Fin (m + 1) → Fin n) (b : Fin m → Fin n) (w : ℂ)
namespace PI.UnitaryGroupMassFormula.QmMove
theorem _root_.solution : Nc E η a b w 0 = ∑ j : Fin (m + 1),
    (((-1 : ℤ) ^ (j : ℕ) : ℤ) : A) * (η (a j) * qminor E (a ∘ j.succAbove) b (w - 1)) := by
  simp only [Nc, sum_perm_fin_succ_eq_sum_cycleRange_decomposeFin (1 : Equiv.Perm (Fin (m + 1))), mul_one]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [qminor, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hs : ((Equiv.Perm.sign (j.cycleRange.symm * Equiv.Perm.decomposeFin.symm (0, σ)) : ℤˣ) : ℤ) =
      (-1 : ℤ) ^ (j : ℕ) * ((Equiv.Perm.sign σ : ℤˣ) : ℤ) := by
    rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_symm, Fin.sign_cycleRange, Equiv.Perm.decomposeFin.symm_sign,
      if_pos rfl, one_mul, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]
  have h0 : Fc E η a b w 0 (j.cycleRange.symm * Equiv.Perm.decomposeFin.symm (0, σ)) 0 = η (a j) := by
    simp [Fc, Equiv.Perm.decomposeFin_symm_apply_zero, Fin.cycleRange_symm_zero]
  have h1 : (fun i : Fin m => Fc E η a b w 0 (j.cycleRange.symm * Equiv.Perm.decomposeFin.symm (0, σ)) i.succ) =
      fun k : Fin m => Tm E (w - 1 - ((k : ℕ) : ℂ)) ((a ∘ j.succAbove) (σ k)) (b k) := by
    funext k
    have hw : w - ((((k : ℕ) + 1 : ℕ)) : ℂ) = w - 1 - ((k : ℕ) : ℂ) := by push_cast; ring
    simp only [Fc, Fin.val_succ, if_neg (Nat.succ_ne_zero _), if_neg (Nat.not_lt_zero _),
      Nat.add_sub_cancel, hw, extN_lt, Equiv.Perm.mul_apply, Equiv.Perm.decomposeFin_symm_apply_succ,
      Equiv.swap_self, Equiv.refl_apply, Fin.cycleRange_symm_succ, Function.comp_apply]
  rw [List.ofFn_succ, List.prod_cons, hs, sgnlem, h0, h1]
end PI.UnitaryGroupMassFormula.QmMove
