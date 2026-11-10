-- Prove2me | solution 1 for PairwiseRealize.sec_A_2_coordinate_face
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-10T02:08:34.115081+00:00
-- url     : https://prove2.me/submissions/f7b954f3-aad7-415d-acde-0737c68b4086

import Mathlib
import Definitions.Def_PairwiseRealize_Model

open PairwiseRealize in
theorem solution (n : ℕ) (i j : Fin n) (hij : i < j) (x : Row n) :
    let flip : Row n → Fin n → Row n := fun y k => Function.update y k (!y k)
    let Δ : Feat n → ℤ := fun f =>
      wvec n x f + wvec n (flip (flip x i) j) f - wvec n (flip x i) f - wvec n (flip x j) f
    Δ Feat.total = 0 ∧ (∀ k, Δ (Feat.single k) = 0) ∧
      (Δ (Feat.pair i j hij) = 1 ∨ Δ (Feat.pair i j hij) = -1) ∧
      ∀ k l (h : k < l), (k, l) ≠ (i, j) → Δ (Feat.pair k l h) = 0 := by
  intro flip Δ
  have hji : j ≠ i := ne_of_gt hij
  have hnot : ∀ b : Bool, bv (!b) = 1 - bv b := by intro b; cases b <;> simp [bv]
  have v1 : ∀ m, flip x i m = if m = i then !x i else x m := by
    intro m; simp only [flip, Function.update_apply]
  have v2 : ∀ m, flip x j m = if m = j then !x j else x m := by
    intro m; simp only [flip, Function.update_apply]
  have v3 : ∀ m, flip (flip x i) j m = if m = j then !x j else if m = i then !x i else x m := by
    intro m
    simp only [flip, Function.update_apply, if_neg hji]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [Δ, wvec]
  · intro k
    simp only [Δ, wvec, v1, v2, v3]
    split_ifs <;> subst_vars <;> (try simp only [hnot]) <;>
      first
        | ring1
        | exact absurd rfl hji
        | exact absurd hij (lt_irrefl _)
  · simp only [Δ, wvec, v1, v2, v3, if_neg hji, if_neg hji.symm, if_true]
    cases x i <;> cases x j <;> simp [bv]
  · intro k l h hne
    simp only [Δ, wvec, v1, v2, v3]
    split_ifs <;> subst_vars <;> (try simp only [hnot]) <;>
      first
        | ring1
        | exact absurd rfl hji
        | exact absurd rfl hne
        | exact absurd h (lt_irrefl _)
        | exact absurd hij (lt_irrefl _)
        | exact absurd (h.trans hij) (lt_irrefl _)
        | exact absurd (hij.trans h) (lt_irrefl _)
