-- Prove2me | solution 1 for ShiShallow.apply1_eq_apply1Matrix_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-13T18:22:10.782684+00:00
-- url     : https://prove2.me/submissions/85c03ecf-90fe-41a5-91d5-aea5165b98f4

import Definitions.Def_ShiShallow_Matrix

set_option autoImplicit false

open ShiShallow

private lemma shiBr_two_point_sum {ι : Type} [Fintype ι] [DecidableEq ι] {A B : ι}
    (hAB : A ≠ B) (F : ι → ℂ)
    (hF : ∀ x, x ≠ A → x ≠ B → F x = 0) :
    ∑ x, F x = F A + F B := by
  have hsub : ({A, B} : Finset ι) ⊆ Finset.univ := Finset.subset_univ _
  have h1 : ∑ x ∈ ({A, B} : Finset ι), F x = ∑ x ∈ Finset.univ, F x := by
    refine Finset.sum_subset hsub ?_
    intro x _ hx
    exact hF x (fun h => hx (by simp [h])) (fun h => hx (by simp [h]))
  rw [← h1]
  exact Finset.sum_pair hAB

private lemma shiBr_update_ne {n : ℕ} (i : Fin n) (y : Bits n) :
    Function.update y i false ≠ Function.update y i true := by
  intro h
  have h1 : Function.update y i false i = Function.update y i true i := congrFun h i
  rw [Function.update_self, Function.update_self] at h1
  exact Bool.false_ne_true h1

private lemma shiBr_guard_update {n : ℕ} (i : Fin n) (y z : Bits n)
    (h : ∀ k, k ∉ ({i} : Finset (Fin n)) → y k = z k) :
    z = Function.update y i (z i) := by
  funext k
  by_cases hk : k = i
  · rw [hk, Function.update_self]
  · rw [Function.update_of_ne hk]
    exact (h k (by simpa [Finset.mem_singleton] using hk)).symm

private lemma shiBr_apply1Matrix_entry {n : ℕ} (U : Matrix Bool Bool ℂ) (i : Fin n)
    (y : Bits n) (b : Bool) :
    apply1Matrix U i y (Function.update y i b) = U (y i) b := by
  have hg : ∀ k, k ∉ ({i} : Finset (Fin n)) → y k = Function.update y i b k := by
    intro k hk
    have hki : k ≠ i := by simpa [Finset.mem_singleton] using hk
    rw [Function.update_of_ne hki]
  first
  | (simp only [apply1Matrix, Matrix.of_apply]; rw [if_pos hg, Function.update_self]; done)
  | (unfold apply1Matrix; rw [Matrix.of_apply, if_pos hg, Function.update_self]; done)
  | (simp only [apply1Matrix, Matrix.of_apply, Function.update_self]; rw [if_pos hg]; done)

private lemma shiBr_apply1Matrix_vanish {n : ℕ} (U : Matrix Bool Bool ℂ) (i : Fin n)
    (y z : Bits n) (h0 : z ≠ Function.update y i false)
    (h1 : z ≠ Function.update y i true) :
    apply1Matrix U i y z = 0 := by
  have hg : ¬ (∀ k, k ∉ ({i} : Finset (Fin n)) → y k = z k) := by
    intro hguard
    have hz : z = Function.update y i (z i) := shiBr_guard_update i y z hguard
    cases hzi : z i
    · exact h0 (hz.trans (by rw [hzi]))
    · exact h1 (hz.trans (by rw [hzi]))
  first
  | (simp only [apply1Matrix, Matrix.of_apply]; rw [if_neg hg]; done)
  | (unfold apply1Matrix; rw [Matrix.of_apply, if_neg hg]; done)
  | (simp only [apply1Matrix, Matrix.of_apply, if_neg hg]; done)

theorem solution {n : ℕ} (U : Matrix Bool Bool ℂ) (i : Fin n)
    (ψ : QState n) :
    apply1 U i ψ = Matrix.mulVec (apply1Matrix U i) ψ := by
  funext y
  have hRHS : Matrix.mulVec (apply1Matrix U i) ψ y
      = ∑ z : Bits n, apply1Matrix U i y z * ψ z :=
    Matrix.mulVec_apply_eq_sum (apply1Matrix U i) ψ y
  have hkey : (∑ z : Bits n, apply1Matrix U i y z * ψ z)
      = apply1Matrix U i y (Function.update y i false) * ψ (Function.update y i false)
        + apply1Matrix U i y (Function.update y i true) * ψ (Function.update y i true) :=
    shiBr_two_point_sum (shiBr_update_ne i y) (fun z => apply1Matrix U i y z * ψ z)
      (fun z h0 h1 => by
        have hv := shiBr_apply1Matrix_vanish U i y z h0 h1
        simp [hv])
  have hLHS : apply1 U i ψ y = ∑ b : Bool, U (y i) b * ψ (Function.update y i b) := rfl
  rw [hLHS, hRHS, hkey]
  simp only [shiBr_apply1Matrix_entry]
  first
  | (rw [Fintype.sum_bool]; exact add_comm _ _)
  | (rw [Fintype.sum_bool]; ring)
  | (simp [Fintype.sum_bool, add_comm]; done)
