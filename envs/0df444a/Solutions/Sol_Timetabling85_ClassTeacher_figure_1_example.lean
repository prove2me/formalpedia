-- Prove2me | solution 1 for Timetabling85.ClassTeacher.figure_1_example
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-12T22:03:57.933179+00:00
-- url     : https://prove2.me/submissions/74aebe8d-3631-4a10-8664-d3d41b300647

import Mathlib
import Definitions.Def_Timetabling85_ClassTeacher_Problems



namespace Timetabling85.ClassTeacher

lemma lo_eq' (s p : ℕ) : lo s p = s / p := by
  unfold lo; exact Nat.floor_div_eq_div s p

lemma hi_eq' (s p : ℕ) (hp : 0 < p) : hi s p = (s + p - 1) / p := by
  unfold hi
  apply le_antisymm
  · apply Nat.ceil_le.mpr
    rw [div_le_iff₀ (by exact_mod_cast hp)]
    have h1 := Nat.div_add_mod (s + p - 1) p
    have h2 := Nat.mod_lt (s + p - 1) hp
    have : s ≤ (s + p - 1) / p * p := by
      generalize (s + p - 1) / p = c at *
      rw [Nat.mul_comm c p]
      omega
    exact_mod_cast this
  · have hk : (s : ℚ) / p ≤ ⌈(s : ℚ) / p⌉₊ := Nat.le_ceil _
    rw [div_le_iff₀ (by exact_mod_cast hp)] at hk
    have hk' : s ≤ ⌈(s : ℚ) / p⌉₊ * p := by exact_mod_cast hk
    generalize ⌈(s : ℚ) / p⌉₊ = k at *
    apply Nat.le_of_lt_succ
    rw [Nat.div_lt_iff_lt_mul hp]
    rw [Nat.succ_mul]
    omega

theorem fig_core :
    IsCT3 (m := 2) (n := 3) ![![1, 2, 4], ![3, 0, 2]] 3
      (fun i j k => (![![![0, 0, 2], ![1, 0, 0]],
                       ![![0, 1, 1], ![1, 0, 1]],
                       ![![1, 1, 1], ![1, 0, 1]]] : Fin 3 → Fin 2 → Fin 3 → ℕ) k i j) := by
  unfold IsCT3 SchedulesAll rowSum colSum
  simp only [lo_eq', hi_eq' _ _ (by norm_num : 0 < 3)]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

end Timetabling85.ClassTeacher

open Timetabling85.ClassTeacher


theorem solution :
    IsCT3 (m := 2) (n := 3) ![![1, 2, 4], ![3, 0, 2]] 3
      (fun i j k => (![![![0, 0, 2], ![1, 0, 0]],
                       ![![0, 1, 1], ![1, 0, 1]],
                       ![![1, 1, 1], ![1, 0, 1]]] : Fin 3 → Fin 2 → Fin 3 → ℕ) k i j) := by
  exact fig_core
