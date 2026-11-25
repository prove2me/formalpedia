-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmMove.Nc_last
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:42:04.433261+00:00
-- url     : https://prove2.me/submissions/68dad127-52b8-4053-a5b6-91a43b6b34dc

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantVectorMove_SumPermEqSumFirstColumnSplit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantVectorMove_MoveOperatorCovariance
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmMove_extN_lt
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
theorem _root_.solution : Nc E η a b w m = ∑ j : Fin (m + 1),
    (((-1 : ℤ) ^ (m - (j : ℕ)) : ℤ) : A) * (qminor E (a ∘ j.succAbove) b w * η (a j)) := by
  simp only [Nc, sum_perm_fin_succ_eq_sum_cycleRange_decomposeFin (finRotate (m + 1))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [qminor, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hjm := j.isLt
  have hu : Equiv.Perm.sign (j.cycleRange.symm * Equiv.Perm.decomposeFin.symm (0, σ) * finRotate (m + 1)) =
      (-1) ^ (m - (j : ℕ)) * Equiv.Perm.sign σ := by
    rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_mul, Equiv.Perm.sign_symm, Fin.sign_cycleRange,
      Equiv.Perm.decomposeFin.symm_sign, if_pos rfl, one_mul, sign_finRotate, Nat.add_sub_cancel, mul_right_comm, ← pow_add,
      show (j : ℕ) + m = (m - (j : ℕ)) + 2 * (j : ℕ) by omega, pow_add, pow_mul, Int.units_sq, one_pow,
      mul_one]
  have hs : ((Equiv.Perm.sign (j.cycleRange.symm * Equiv.Perm.decomposeFin.symm (0, σ) * finRotate (m + 1)) : ℤˣ) : ℤ) =
      (-1 : ℤ) ^ (m - (j : ℕ)) * ((Equiv.Perm.sign σ : ℤˣ) : ℤ) := by
    rw [hu, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]
  have h0 : Fc E η a b w m (j.cycleRange.symm * Equiv.Perm.decomposeFin.symm (0, σ) * finRotate (m + 1))
      (Fin.last m) = η (a j) := by
    simp [Fc, finRotate_last, Equiv.Perm.decomposeFin_symm_apply_zero, Fin.cycleRange_symm_zero]
  have h1 : (fun i : Fin m => Fc E η a b w m
      (j.cycleRange.symm * Equiv.Perm.decomposeFin.symm (0, σ) * finRotate (m + 1)) i.castSucc) =
      fun k : Fin m => Tm E (w - ((k : ℕ) : ℂ)) ((a ∘ j.succAbove) (σ k)) (b k) := by
    funext k
    have hk := k.isLt
    have hr : finRotate (m + 1) k.castSucc = k.succ := by
      ext
      rw [coe_finRotate_of_ne_last (Fin.castSucc_lt_last k).ne]
      simp
    simp only [Fc, Fin.coe_castSucc, if_neg (Nat.ne_of_lt hk), if_pos hk, extN_lt, Equiv.Perm.mul_apply, hr,
      Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self, Equiv.refl_apply, Fin.cycleRange_symm_succ,
      Function.comp_apply]
  rw [List.ofFn_succ', List.concat_eq_append, List.prod_append, List.prod_cons, List.prod_nil, mul_one,
    hs, h0, h1]
  simp only [Int.cast_mul, mul_assoc]
end PI.UnitaryGroupMassFormula.QmMove
