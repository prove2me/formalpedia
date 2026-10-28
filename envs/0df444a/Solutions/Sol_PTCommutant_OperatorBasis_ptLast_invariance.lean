-- Prove2me | solution 1 for PTCommutant.OperatorBasis.ptLast_invariance
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T21:23:46.50266+00:00
-- url     : https://prove2.me/submissions/a31fd97c-fcb5-4cb1-a286-4b6f866f7f7a

import Mathlib
import Definitions.Def_PTCommutant_OperatorBasis_Model

open QAlgorithms.Schur PTCommutant.OperatorBasis

lemma tpL_left {d n : ℕ} (a : Equiv.Perm (Fin n)) (M : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ)
    (x z : Fin n → Fin d) : (tensorPermutation d n a * M) x z = M (x ∘ a) z := by
  rw [Matrix.mul_apply]
  have : ∀ y : Fin n → Fin d, tensorPermutation d n a x y = if x ∘ a = y then 1 else 0 := by
    intro y
    unfold tensorPermutation
    simp only [Matrix.of_apply]
    congr 1
    apply propext
    constructor
    · rintro rfl; funext i; simp
    · rintro rfl; funext i; simp
  simp only [this, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

lemma tpL_right {d n : ℕ} (b : Equiv.Perm (Fin n)) (M : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ)
    (x z : Fin n → Fin d) : (M * tensorPermutation d n b) x z = M x (z ∘ b.symm) := by
  rw [Matrix.mul_apply]
  unfold tensorPermutation
  simp only [Matrix.of_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

lemma tpL_mul {d n : ℕ} (a b : Equiv.Perm (Fin n)) :
    tensorPermutation d n a * tensorPermutation d n b = tensorPermutation d n (a * b) := by
  ext x z
  rw [tpL_left]
  unfold tensorPermutation
  simp only [Matrix.of_apply]
  congr 1
  apply propext
  constructor
  · intro h; funext i
    have := congrFun h (a.symm i)
    simpa [Equiv.Perm.mul_def] using this
  · intro h; funext i
    rw [h]; simp [Equiv.Perm.mul_def]

lemma lift_last {k : ℕ} (ρ : Equiv.Perm (Fin (k + 1))) :
    liftPerm (k + 1) 1 ρ (Fin.last (k + 1)) = Fin.last (k + 1) := by
  unfold liftPerm
  simp only [Equiv.Perm.extendDomainHom_apply]
  apply Equiv.Perm.extendDomain_apply_not_subtype
  simp

lemma fix_iff {n : ℕ} (L : Equiv.Perm (Fin (n + 1))) (hL : L (Fin.last n) = Fin.last n)
    (i : Fin (n + 1)) : L i = Fin.last n ↔ i = Fin.last n := by
  constructor
  · intro h; rw [← hL] at h; exact L.injective h
  · rintro rfl; exact hL

lemma fix_symm {n : ℕ} (L : Equiv.Perm (Fin (n + 1))) (hL : L (Fin.last n) = Fin.last n) :
    L.symm (Fin.last n) = Fin.last n := by
  rw [Equiv.symm_apply_eq]; exact hL.symm

lemma upd_comp {d n : ℕ} (L : Equiv.Perm (Fin (n + 1))) (hL : L (Fin.last n) = Fin.last n)
    (x : Fin (n + 1) → Fin d) (v : Fin d) :
    Function.update x (Fin.last n) v ∘ L = Function.update (x ∘ L) (Fin.last n) v := by
  funext i
  simp only [Function.comp_apply, Function.update_apply, fix_iff L hL]

theorem solution {d k : ℕ} (ρ ρ' : Equiv.Perm (Fin (k + 1)))
    (τ : Equiv.Perm (Fin (k + 2))) :
    ptLast (tensorPermutation d (k + 2) (liftPerm (k + 1) 1 ρ)) =
        tensorPermutation d (k + 2) (liftPerm (k + 1) 1 ρ) ∧
      tensorPermutation d (k + 2) (liftPerm (k + 1) 1 ρ) *
          ptLast (tensorPermutation d (k + 2) τ) *
          tensorPermutation d (k + 2) (liftPerm (k + 1) 1 ρ') =
        ptLast (tensorPermutation d (k + 2)
          (liftPerm (k + 1) 1 ρ * τ * liftPerm (k + 1) 1 ρ')) := by
  set L := liftPerm (k + 1) 1 ρ with hLdef
  set L' := liftPerm (k + 1) 1 ρ' with hL'def
  have hL : L (Fin.last (k + 1)) = Fin.last (k + 1) := lift_last ρ
  have hL' : L' (Fin.last (k + 1)) = Fin.last (k + 1) := lift_last ρ'
  have hLs := fix_symm L hL
  have hL's := fix_symm L' hL'
  constructor
  · ext x y
    unfold ptLast tensorPermutation
    simp only [Matrix.of_apply]
    simp only [upd_comp L.symm hLs]
    apply if_congr _ rfl rfl
    rw [funext_iff, funext_iff]
    constructor
    · intro h i
      by_cases hi : i = Fin.last (k + 1)
      · subst hi
        have := h (Fin.last (k + 1))
        simp only [Function.update_self, Function.comp_apply, hLs] at this ⊢
        exact this.symm
      · have := h i
        simpa [Function.update_of_ne hi] using this
    · intro h i
      by_cases hi : i = Fin.last (k + 1)
      · subst hi
        have := h (Fin.last (k + 1))
        simp only [Function.update_self, Function.comp_apply, hLs] at this ⊢
        exact this.symm
      · have := h i
        simpa [Function.update_of_ne hi] using this
  · ext x z
    rw [tpL_right, tpL_left]
    conv_rhs => unfold ptLast; rw [Matrix.of_apply, ← tpL_mul, ← tpL_mul, tpL_right, tpL_left]
    unfold ptLast
    simp only [Matrix.of_apply, Function.comp_apply, hL, hL's]
    rw [upd_comp L hL, upd_comp L'.symm hL's]
