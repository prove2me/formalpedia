-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Extend50.P28.proposition45
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-29T09:33:14.643707+00:00
-- url     : https://prove2.me/submissions/cd9584b5-8ba9-4d20-9b40-e39b13569b86

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P28

namespace QAlgorithms.Papers.Independent.Extend50.P28

lemma card_fixed (d N : ℕ) (a : Fin N) :
    Fintype.card {x : Fin (N + 1) → Fin d // x a.castSucc = x (Fin.last N)} = d ^ N := by
  have e : {x : Fin (N + 1) → Fin d // x a.castSucc = x (Fin.last N)} ≃ (Fin N → Fin d) :=
    { toFun := fun x i => x.1 i.castSucc
      invFun := fun w => ⟨Fin.snoc w (w a), by simp⟩
      left_inv := by
        rintro ⟨x, hx⟩
        apply Subtype.ext
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp [hx]
        · simp
      right_inv := by
        intro w; funext i; simp }
  rw [Fintype.card_congr e]; simp

lemma tr_ts (d N : ℕ) (a : Fin N) : (transposedSwap d N a).trace = (d : ℂ) ^ N := by
  have h1 : ∀ x : Fin (N + 1) → Fin d,
      transposedSwap d N a x x = if x a.castSucc = x (Fin.last N) then 1 else 0 := by
    intro x
    simp only [transposedSwap, lastPartialTranspose, Function.update_eq_self,
      QAlgorithms.Schur.tensorPermutation, Matrix.of_apply]
    rw [Equiv.symm_swap]
    have hne : a.castSucc ≠ Fin.last N := Fin.castSucc_lt_last a |>.ne
    have hiff : x = x ∘ ⇑(Equiv.swap a.castSucc (Fin.last N)) ↔ x a.castSucc = x (Fin.last N) := by
      constructor
      · intro h
        have := congrFun h a.castSucc
        simpa using this
      · intro h
        funext i
        by_cases h1 : i = a.castSucc
        · subst h1; simp [h]
        · by_cases h2 : i = Fin.last N
          · subst h2; simp [h]
          · simp [Equiv.swap_apply_of_ne_of_ne h1 h2]
    simp only [hiff]
  unfold Matrix.trace
  simp only [Matrix.diag_apply, h1]
  rw [Finset.sum_boole]
  have := card_fixed d N a
  rw [Fintype.card_subtype] at this
  rw [this]; simp

end QAlgorithms.Papers.Independent.Extend50.P28

open QAlgorithms.Papers.Independent.Extend50.P28 in
theorem solution (n d : ℕ) (hn : 2 ≤ n) (hd : 2 ≤ d) :
    (pbtOperator d (n - 1)).trace = (((n : ℂ) - 1) * (d : ℂ) ^ (n - 1)) := by
  unfold pbtOperator
  rw [Matrix.trace_sum]
  simp only [tr_ts]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : ((n - 1 : ℕ) : ℂ) = (n : ℂ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  rw [this]
