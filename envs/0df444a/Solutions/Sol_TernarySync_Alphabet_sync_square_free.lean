-- Prove2me | solution 1 for TernarySync.Alphabet.sync_square_free
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:25:13.293343+00:00
-- url     : https://prove2.me/submissions/f16a3442-cb17-4a6f-a754-b76a7c3e43b5

import Mathlib
import Definitions.Def_TernarySync_Alphabet_SyncString

section
set_option autoImplicit false

namespace TernarySync.Dev.SyncSqFree
open TernarySync.Alphabet

theorem ed_self {α : Type*} (X : List α) : ed X X = 0 :=
  Nat.eq_zero_of_le_zero (Nat.sInf_le (IDScript.refl X))

theorem factor_shift {α : Type*} (p F s : List α) (i j : ℕ) (hij : i ≤ j) (hj : j ≤ F.length) :
    factor (p ++ F ++ s) (p.length + i) (p.length + j) = factor F i j := by
  unfold factor
  rw [List.append_assoc, show p.length + j - (p.length + i) = j - i by omega, List.drop_length_add_append,
    List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]

end TernarySync.Dev.SyncSqFree

namespace TernarySync.Alphabet
open TernarySync.Dev.SyncSqFree in
theorem chk_sync_square_free {α : Type*} (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1) (S : List α) :
    (IsSyncString ε S → IsSquareFree S) ∧
      (∀ F : List α, F <:+: S → IsSyncString ε S → IsSyncString ε F) ∧
      (∀ F : List α, F <:+: S → IsSquareFree S → IsSquareFree F) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hS w hw ⟨X, hX, hwX⟩
    obtain ⟨p, s, hps⟩ := hw
    subst hwX
    have hlen : 0 < X.length := List.length_pos_iff.2 hX
    have hS' := hS p.length (p.length + X.length) (p.length + X.length + X.length)
      (by omega) (by omega) (by rw [← hps]; simp; omega)
    have e1 : factor S p.length (p.length + X.length) = X := by
      rw [← hps]
      have := factor_shift p (X ++ X) s 0 X.length (by omega) (by simp)
      simp only [Nat.add_zero] at this
      rw [this]; simp [factor]
    have e2 : factor S (p.length + X.length) (p.length + X.length + X.length) = X := by
      rw [← hps]
      have := factor_shift p (X ++ X) s X.length (X.length + X.length) (by omega) (by simp)
      rw [← add_assoc] at this
      rw [this]; simp [factor]
    rw [e1, e2, ed_self] at hS'
    have : (0 : ℝ) < (1 - ε) * ((((p.length + X.length + X.length : ℕ) : ℝ)) -
      ((p.length : ℕ) : ℝ)) := by
      apply mul_pos (by linarith)
      have : (0 : ℝ) < X.length := by exact_mod_cast hlen
      push_cast; linarith
    push_cast at this hS'
    linarith
  · intro F hF hS i j k hij hjk hk
    obtain ⟨p, s, hps⟩ := hF
    have := hS (p.length + i) (p.length + j) (p.length + k) (by omega) (by omega)
      (by rw [← hps]; simp; omega)
    rw [← hps, factor_shift p F s i j (by omega) (by omega),
      factor_shift p F s j k (by omega) (by omega)] at this
    push_cast at this
    have e : ((p.length : ℝ) + k) - (p.length + i) = (k : ℝ) - i := by ring
    rw [e] at this
    exact this
  · intro F hF hS w hw
    exact hS w (hw.trans hF)
end TernarySync.Alphabet
end

theorem solution : type_of% @TernarySync.Alphabet.chk_sync_square_free := @TernarySync.Alphabet.chk_sync_square_free
