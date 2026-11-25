-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmMove.stepC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:52:13.172154+00:00
-- url     : https://prove2.me/submissions/eefb9d57-c0f2-4f82-be2c-1e08901ff823

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantVectorMove_SumPermEqSumFirstColumnSplit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantVectorMove_MoveOperatorCovariance
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmMove_midC
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
private lemma list_prod_eq_take_mul_pair_mul_drop {M : Type*} [Monoid M] (l : List M) (i : ℕ) (h : i + 1 < l.length) :
    l.prod = (l.take i).prod * (l[i] * l[i + 1]) * (l.drop (i + 1 + 1)).prod := by
  induction l generalizing i with
  | nil => simp at h
  | cons x l ih =>
    cases i with
    | zero =>
      cases l with
      | nil => simp at h
      | cons y l =>
        rw [List.getElem_cons_succ, List.getElem_cons_zero, List.getElem_cons_zero, List.take_zero,
          List.drop_succ_cons, List.drop_succ_cons, List.drop_zero, List.prod_nil, one_mul,
          List.prod_cons, List.prod_cons, mul_assoc]
    | succ i =>
      have h' : i + 1 < l.length := by simp only [List.length_cons] at h; omega
      rw [List.prod_cons, ih i h', List.take_succ_cons, List.prod_cons, List.getElem_cons_succ,
        List.getElem_cons_succ, List.drop_succ_cons]
      simp only [mul_assoc]
private lemma sum_perm_eq_zero_of_mul_right_eq_neg {B : Type*} [Ring B] [Algebra ℂ B] {k : ℕ} (s : Equiv.Perm (Fin k))
    (G : Equiv.Perm (Fin k) → B) (h : ∀ τ, G (τ * s) = -G τ) : ∑ τ, G τ = 0 := by
  have h1 : ∑ τ, G τ = -∑ τ, G τ := by
    rw [← Finset.sum_neg_distrib, ← Equiv.sum_comp (Equiv.mulRight s)]
    exact Finset.sum_congr rfl fun τ _ => h τ
  have h2 : ∑ τ, G τ + ∑ τ, G τ = 0 := by
    rw [← sub_neg_eq_add, ← h1, sub_self]
  calc ∑ τ, G τ = (2 : ℂ)⁻¹ • ((2 : ℂ) • ∑ τ, G τ) := by
        rw [smul_smul, inv_mul_cancel₀ (two_ne_zero : (2 : ℂ) ≠ 0), one_smul]
    _ = 0 := by rw [two_smul, h2, smul_zero]
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
theorem _root_.solution (hη : ∀ a b c, E a b * η c - η c * E a b = if b = c then η a else 0)
    (p : ℕ) (hp : p < m) : Nc E η a b w (p + 1) = -Nc E η a b w p := by
  have hp0 : p < m + 1 := by omega
  have hp1 : p + 1 < m + 1 := by omega
  obtain ⟨s, hs⟩ : ∃ s : Equiv.Perm (Fin (m + 1)), s = Equiv.swap ⟨p, hp0⟩ ⟨p + 1, hp1⟩ := ⟨_, rfl⟩
  have hne : (⟨p, hp0⟩ : Fin (m + 1)) ≠ ⟨p + 1, hp1⟩ := by
    intro h
    have := congrArg Fin.val h
    simp at this
  have hsP : s ⟨p, hp0⟩ = ⟨p + 1, hp1⟩ := by rw [hs, Equiv.swap_apply_left]
  have hsP1 : s ⟨p + 1, hp1⟩ = ⟨p, hp0⟩ := by rw [hs, Equiv.swap_apply_right]
  have hsq : ∀ q : Fin (m + 1), (q : ℕ) ≠ p → (q : ℕ) ≠ p + 1 → s q = q := by
    intro q h1 h2
    rw [hs]
    exact Equiv.swap_apply_of_ne_of_ne (fun h => h1 (by rw [h])) (fun h => h2 (by rw [h]))
  have hsgn : ∀ τ : Equiv.Perm (Fin (m + 1)),
      ((Equiv.Perm.sign (τ * s) : ℤ) : A) = -((Equiv.Perm.sign τ : ℤ) : A) := by
    intro τ
    rw [hs, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hne, mul_neg_one, Units.val_neg, Int.cast_neg]
  have hoff : ∀ (τ : Equiv.Perm (Fin (m + 1))) (q : Fin (m + 1)), (q : ℕ) ≠ p → (q : ℕ) ≠ p + 1 →
      Fc E η a b w (p + 1) τ q = Fc E η a b w p (τ * s) q := by
    intro τ q h1 h2
    simp only [Fc, Equiv.Perm.mul_apply, hsq q h1 h2, if_neg h1, if_neg h2]
    by_cases hq : (q : ℕ) < p
    · rw [if_pos hq, if_pos (show (q : ℕ) < p + 1 by omega)]
    · rw [if_neg hq, if_neg (show ¬ (q : ℕ) < p + 1 by omega)]
  have hoff2 : ∀ (τ : Equiv.Perm (Fin (m + 1))) (q : Fin (m + 1)), (q : ℕ) ≠ p → (q : ℕ) ≠ p + 1 →
      Fc E η a b w (p + 1) (τ * s) q = Fc E η a b w (p + 1) τ q := by
    intro τ q h1 h2
    simp only [Fc, Equiv.Perm.mul_apply, hsq q h1 h2]
  have hT : ∀ τ : Equiv.Perm (Fin (m + 1)), (List.ofFn (Fc E η a b w p (τ * s))).take p =
      (List.ofFn (Fc E η a b w (p + 1) τ)).take p := by
    intro τ
    apply List.ext_getElem (by simp)
    intro k h1 h2
    simp only [List.getElem_take, List.getElem_ofFn]
    simp only [List.length_take, List.length_ofFn] at h1
    exact (hoff τ _ (by show k ≠ p; omega) (by show k ≠ p + 1; omega)).symm
  have hD : ∀ τ : Equiv.Perm (Fin (m + 1)), (List.ofFn (Fc E η a b w p (τ * s))).drop (p + 1 + 1) =
      (List.ofFn (Fc E η a b w (p + 1) τ)).drop (p + 1 + 1) := by
    intro τ
    apply List.ext_getElem (by simp)
    intro k h1 h2
    simp only [List.getElem_drop, List.getElem_ofFn]
    exact (hoff τ _ (by show p + 1 + 1 + k ≠ p; omega) (by show p + 1 + 1 + k ≠ p + 1; omega)).symm
  have hT2 : ∀ τ : Equiv.Perm (Fin (m + 1)), (List.ofFn (Fc E η a b w (p + 1) (τ * s))).take p =
      (List.ofFn (Fc E η a b w (p + 1) τ)).take p := by
    intro τ
    apply List.ext_getElem (by simp)
    intro k h1 h2
    simp only [List.getElem_take, List.getElem_ofFn]
    simp only [List.length_take, List.length_ofFn] at h1
    exact hoff2 τ _ (by show k ≠ p; omega) (by show k ≠ p + 1; omega)
  have hD2 : ∀ τ : Equiv.Perm (Fin (m + 1)), (List.ofFn (Fc E η a b w (p + 1) (τ * s))).drop (p + 1 + 1) =
      (List.ofFn (Fc E η a b w (p + 1) τ)).drop (p + 1 + 1) := by
    intro τ
    apply List.ext_getElem (by simp)
    intro k h1 h2
    simp only [List.getElem_drop, List.getElem_ofFn]
    exact hoff2 τ _ (by show p + 1 + 1 + k ≠ p; omega) (by show p + 1 + 1 + k ≠ p + 1; omega)
  have e1 : ∀ τ : Equiv.Perm (Fin (m + 1)), Fc E η a b w (p + 1) τ ⟨p, hp0⟩ =
      Tm E (w - (p : ℂ)) (a (τ ⟨p, hp0⟩)) (extN b (a 0) p) := by
    intro τ; simp [Fc]
  have e2 : ∀ τ : Equiv.Perm (Fin (m + 1)), Fc E η a b w (p + 1) τ ⟨p + 1, hp1⟩ =
      η (a (τ ⟨p + 1, hp1⟩)) := by
    intro τ; simp [Fc]
  have e3 : ∀ τ : Equiv.Perm (Fin (m + 1)), Fc E η a b w p (τ * s) ⟨p, hp0⟩ =
      η (a (τ ⟨p + 1, hp1⟩)) := by
    intro τ; simp [Fc, hsP]
  have e4 : ∀ τ : Equiv.Perm (Fin (m + 1)), Fc E η a b w p (τ * s) ⟨p + 1, hp1⟩ =
      Tm E (w - ((p : ℂ) + 1)) (a (τ ⟨p, hp0⟩)) (extN b (a 0) p) := by
    intro τ; simp [Fc, hsP1]
  have key : ∀ τ : Equiv.Perm (Fin (m + 1)),
      (List.ofFn (Fc E η a b w (p + 1) τ)).prod - (List.ofFn (Fc E η a b w p (τ * s))).prod =
        ((List.ofFn (Fc E η a b w (p + 1) τ)).take p).prod *
          symC η (extN b (a 0) p) (a (τ ⟨p, hp0⟩)) (a (τ ⟨p + 1, hp1⟩)) *
          ((List.ofFn (Fc E η a b w (p + 1) τ)).drop (p + 1 + 1)).prod := by
    intro τ
    rw [list_prod_eq_take_mul_pair_mul_drop (List.ofFn (Fc E η a b w (p + 1) τ)) p (by simp; omega),
      list_prod_eq_take_mul_pair_mul_drop (List.ofFn (Fc E η a b w p (τ * s))) p (by simp; omega), hT τ, hD τ,
      ← sub_mul, ← mul_sub]
    congr 2
    simp only [List.getElem_ofFn]
    rw [e1 τ, e2 τ, e3 τ, e4 τ]
    have h := congrArg Neg.neg (midC E η hη (w - (p : ℂ)) (w - ((p : ℂ) + 1)) (by ring)
      (a (τ ⟨p, hp0⟩)) (extN b (a 0) p) (a (τ ⟨p + 1, hp1⟩)))
    rw [neg_sub, neg_neg] at h
    exact h
  have hA : Nc E η a b w p = ∑ τ : Equiv.Perm (Fin (m + 1)),
      ((Equiv.Perm.sign (τ * s) : ℤ) : A) * (List.ofFn (Fc E η a b w p (τ * s))).prod :=
    (Equiv.sum_comp (Equiv.mulRight s)
      (fun τ => ((Equiv.Perm.sign τ : ℤ) : A) * (List.ofFn (Fc E η a b w p τ)).prod)).symm
  rw [hA, Nc]
  simp only [hsgn, neg_mul, Finset.sum_neg_distrib, neg_neg]
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
  simp only [← mul_sub, key]
  apply sum_perm_eq_zero_of_mul_right_eq_neg s
  intro τ
  have hS2 : symC η (extN b (a 0) p) (a ((τ * s) ⟨p, hp0⟩)) (a ((τ * s) ⟨p + 1, hp1⟩)) =
      symC η (extN b (a 0) p) (a (τ ⟨p, hp0⟩)) (a (τ ⟨p + 1, hp1⟩)) := by
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hsP, hsP1, symC, symC, add_comm]
  simp only [hsgn, hT2, hD2, hS2, neg_mul]
end PI.UnitaryGroupMassFormula.QmMove
