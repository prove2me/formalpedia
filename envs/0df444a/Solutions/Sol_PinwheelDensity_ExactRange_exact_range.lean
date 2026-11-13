-- Prove2me | solution 1 for PinwheelDensity.ExactRange.exact_range
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T09:11:19.412888+00:00
-- url     : https://prove2.me/submissions/56462303-91b7-414c-9972-1ec602596978
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_PinwheelDensity_ExactRange_Schedulable
import Definitions.Def_PinwheelDensity_ExactRange_coreP
import Theorems.Thm_PinwheelDensity_ExactRange_theorem_1_2
import Theorems.Thm_PinwheelDensity_ExactRange_theorem_1_3
import Theorems.Thm_PinwheelDensity_ExactRange_theorem_1_4
import Theorems.Thm_PinwheelDensity_ExactRange_prop_2_3
import Theorems.Thm_pinwheel_conjecture

section
set_option autoImplicit false

namespace PinwheelDensity.ExactRange.Dev.EX

open PinwheelDensity.ExactRange

theorem density_eq (A : List ℕ) :
    density A = (A.map (fun a : ℕ => (1 : ℚ) / (a : ℚ))).sum := by
  unfold density
  induction A with
  | nil => simp
  | cons a l ih => simp_all

theorem density_fin (A : List ℕ) :
    ∑ i : Fin A.length, (1 : ℚ) / (A.get i : ℕ) = density A := by
  rw [density_eq]
  conv_rhs => rw [← List.ofFn_get A, List.map_ofFn, List.sum_ofFn]
  rfl

theorem sched_of_five_sixths (A : List ℕ) (hpos : ∀ a ∈ A, 1 ≤ a) (hne : A ≠ [])
    (hd : density A ≤ 5 / 6) : Schedulable A := by
  have hk : 1 ≤ A.length := List.length_pos_iff.mpr hne
  obtain ⟨sch, hsch⟩ := pinwheel_conjecture A.length hk A.get
    (fun i => hpos _ (List.get_mem _ _)) (by rw [density_fin]; exact hd)
  exact ⟨fun d => some (sch d), fun i t => by
    obtain ⟨m, h1, h2, h3⟩ := hsch i t
    exact ⟨m, h1, h2, by simp [h3]⟩⟩

theorem density_nonneg (A : List ℕ) : 0 ≤ density A := by
  rw [density_eq]
  apply List.sum_nonneg
  intro x hx
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hx
  positivity

theorem conj_one : ConjectureAt 1 := by
  intro A hpos ⟨hm, _⟩ hd
  have hperm := List.perm_cons_erase hm
  set B := A.erase 1 with hB
  have hdens : density A = 1 / (1 : ℚ) + density B := by
    rw [density_eq, density_eq, hperm.map _ |>.sum_eq]
    simp
  have hc : c 1 = 1 := by norm_num [c]
  have hBnn := density_nonneg B
  have hB0 : density B = 0 := by rw [hc] at hd; simp at hdens; linarith
  have hBnil : B = [] := by
    by_contra hne
    obtain ⟨b, hb⟩ := List.exists_mem_of_ne_nil _ hne
    have hbpos : 1 ≤ b := hpos b (List.mem_of_mem_erase hb)
    have : (1 : ℚ) / b ≤ density B := by
      rw [density_eq]
      have : (1 : ℚ) / b ∈ B.map (fun a : ℕ => (1 : ℚ) / (a : ℚ)) :=
        List.mem_map.mpr ⟨b, hb, rfl⟩
      exact List.single_le_sum (fun x hx => by
        obtain ⟨a, _, rfl⟩ := List.mem_map.mp hx
        positivity) _ this
    have hbq : (0 : ℚ) < 1 / b := by
      have : (0 : ℚ) < b := by exact_mod_cast hbpos
      positivity
    linarith
  rw [hBnil] at hperm
  have hA : A = [1] := by simpa using hperm.eq_singleton  
  subst hA
  have h0 : ∀ i : Fin [1].length, i = ⟨0, by simp⟩ := fun i =>
    Fin.ext (by have := i.2; simp at this ⊢)
  exact ⟨fun _ => some ⟨0, by simp⟩, fun i t => ⟨t, le_refl _, by
    rw [h0 i]; simp, by rw [h0 i]⟩⟩

theorem conj_small (m : ℕ) (h2 : 2 ≤ m) (h3 : m ≤ 3) : ConjectureAt m := by
  intro A hpos ⟨hm, _⟩ hd
  have hne : A ≠ [] := List.ne_nil_of_mem hm
  apply sched_of_five_sixths A hpos hne
  have : c m = 5 / 6 := by
    interval_cases m <;> norm_num [c]
  rwa [this] at hd

theorem threshold_bdd : BddAbove (ThresholdSet 6) := by
  refine ⟨((c 6 + 1 / 6 : ℚ) : ℝ), fun δ hδ => ?_⟩
  by_contra hlt
  push Not at hlt
  obtain ⟨hns, hden⟩ := (prop_2_3 6 (by norm_num)).1 6 (by norm_num)
  apply hns
  apply hδ _ _ (le_of_lt (by rw [hden]; push_cast at hlt ⊢; linarith))
  intro a ha
  simp [sharpCore] at ha
  omega

theorem main : (∀ m : ℕ, 1 ≤ m → (ConjectureAt m ↔ m ≤ 5)) ∧
    (13 / 15 : ℝ) ≤ G 6 ∧ G 6 ≤ (3091 / 3510 : ℝ) ∧ (3091 / 3510 : ℝ) < 37 / 42 := by
  have t12 := theorem_1_2
  have t13 := theorem_1_3
  have t14 := theorem_1_4
  refine ⟨?_, ?_, ?_, by norm_num⟩
  · intro m hm
    constructor
    · intro h
      by_contra hlt
      push Not at hlt
      obtain ⟨A, hp, hmin, hd, hns⟩ := (t14.1 m hlt).1
      exact hns (h A hp hmin hd)
    · intro hle
      interval_cases m
      · exact conj_one
      · exact conj_small 2 le_rfl (by norm_num)
      · exact conj_small 3 (by norm_num) le_rfl
      · intro A hpos ⟨hm4, hmin⟩ hd
        refine t12.1 A (fun a ha => ⟨hpos a ha, hmin a ha⟩) ?_
        have : c 4 = 17 / 20 := by norm_num [c]
        rwa [this] at hd
      · intro A hpos ⟨hm4, hmin⟩ hd
        refine t13.1 A (fun a ha => ⟨hpos a ha, hmin a ha⟩) ?_
        have : c 5 = 13 / 15 := by norm_num [c]
        rwa [this] at hd
  · apply le_csSup threshold_bdd
    intro A hA hd
    exact t13.2.2.1 A (fun a ha => ⟨(hA a ha).1, by have := (hA a ha).2; omega⟩) hd
  · have h := (t14.1 6 le_rfl).2.2.2.2.1
    have : (c 6 - g 6 : ℚ) = 3091 / 3510 := by norm_num [c, g]
    rw [this] at h
    have e : (((3091 / 3510 : ℚ)) : ℝ) = 3091 / 3510 := by norm_num
    rw [e] at h; exact h

end PinwheelDensity.ExactRange.Dev.EX

namespace PinwheelDensity.ExactRange

theorem chk_exact_range :
    (∀ m : ℕ, 1 ≤ m → (ConjectureAt m ↔ m ≤ 5)) ∧
    (13 / 15 : ℝ) ≤ G 6 ∧ G 6 ≤ (3091 / 3510 : ℝ) ∧ (3091 / 3510 : ℝ) < 37 / 42 :=
  Dev.EX.main

end PinwheelDensity.ExactRange
end

theorem solution : type_of% @PinwheelDensity.ExactRange.chk_exact_range := @PinwheelDensity.ExactRange.chk_exact_range
