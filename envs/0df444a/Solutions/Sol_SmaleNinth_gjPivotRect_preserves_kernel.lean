-- Prove2me | solution 1 for SmaleNinth.gjPivotRect_preserves_kernel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-25T08:50:52.157528+00:00
-- url     : https://prove2.me/submissions/98479f1b-a548-41f6-9d95-e11a979d74f6

import Definitions.Def_SmaleNinth_GaussJordanPlus
import Theorems.Thm_SmaleNinth_gjPivotRect_mulVec_apply

open Matrix SmaleNinth

theorem solution {r c : ℕ}
    (S : Matrix (Fin r) (Fin c) ℝ) (i : Fin r) (j : Fin c)
    (hp : S i j ≠ 0) :
    (∀ z : Fin c → ℝ, S.mulVec z = 0) ↔
      ∀ z : Fin c → ℝ, (SmaleNinth.gjPivotRect S i j).mulVec z = 0 := by
  constructor
  · intro h z
    have hz := h z
    funext a
    have hf := SmaleNinth.gjPivotRect_mulVec_apply S i j z a
    rw [hf]
    by_cases hai : a = i
    · subst a
      simp only [if_pos rfl]
      have hi : S.mulVec z i = 0 := by
        change S.mulVec z i = 0
        exact congrFun hz i
      exact div_eq_zero_iff.mpr (Or.inl hi)
    · simp only [if_neg hai]
      have hi : S.mulVec z i = 0 := by
        change S.mulVec z i = 0
        exact congrFun hz i
      have ha : S.mulVec z a = 0 := by
        change S.mulVec z a = 0
        exact congrFun hz a
      rw [hi, ha]
      ring
      rfl
  · intro h z
    have hz := h z
    funext a
    by_cases hai : a = i
    · subst a
      have hi := congrFun hz i
      have hf := SmaleNinth.gjPivotRect_mulVec_apply S i j z i
      rw [hf] at hi
      simp only [if_pos rfl] at hi
      have hdiv : S.mulVec z i / S i j = 0 := by
        change S.mulVec z i / S i j = 0 at hi
        exact hi
      change S.mulVec z i = 0
      exact (div_eq_zero_iff.mp hdiv).resolve_right hp
    · have hi := congrFun hz i
      have ha := congrFun hz a
      have hfi := SmaleNinth.gjPivotRect_mulVec_apply S i j z i
      have hfa := SmaleNinth.gjPivotRect_mulVec_apply S i j z a
      rw [hfi] at hi
      rw [hfa] at ha
      simp only [if_pos rfl] at hi
      simp only [if_neg hai] at ha
      have hdiv : S.mulVec z i / S i j = 0 := by
        change S.mulVec z i / S i j = 0 at hi
        exact hi
      have hpi0 : S.mulVec z i = 0 :=
        (div_eq_zero_iff.mp hdiv).resolve_right hp
      change S.mulVec z a = 0
      rw [hpi0] at ha
      simpa using ha
