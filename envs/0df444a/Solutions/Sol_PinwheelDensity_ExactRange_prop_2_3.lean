-- Prove2me | solution 1 for PinwheelDensity.ExactRange.prop_2_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T08:27:54.329944+00:00
-- url     : https://prove2.me/submissions/f88bad9d-ab67-4e16-89b7-b4bf749111ab

import Mathlib
import Definitions.Def_PinwheelDensity_ExactRange_Schedulable
import Definitions.Def_PinwheelDensity_ExactRange_coreP
import Theorems.Thm_PinwheelDensity_ExactRange_lemma_2_1
import Theorems.Thm_PinwheelDensity_ExactRange_lemma_2_2
import Theorems.Thm_PinwheelDensity_ExactRange_lemma_A_1

section
set_option autoImplicit false

namespace PinwheelDensity.ExactRange.Dev.P23

open PinwheelDensity.ExactRange

lemma notSched (P : List ℕ) (hP : ∀ a ∈ P, 1 ≤ a) (hfree : NoScheduleWithFreeDay P)
    (x : ℕ) (hx : 1 ≤ x) : ¬ Schedulable (P ++ [x]) := by
  intro h
  have hpos : ∀ a ∈ P ++ [x], 1 ≤ a := by
    intro a ha
    rcases List.mem_append.1 ha with h | h
    · exact hP a h
    · simp at h; omega
  have h1 := (PinwheelDensity.ExactRange.lemma_A_1.2.1 _ hpos).2 h
  have h2 := (PinwheelDensity.ExactRange.lemma_A_1.2.2 (P ++ [x]) (by simp) hpos).2.1 h1
  exact PinwheelDensity.ExactRange.lemma_2_1 P hP hfree x hx h2

lemma sharpCore_pos (m : ℕ) (hm : 1 ≤ m) : ∀ a ∈ sharpCore m, 1 ≤ a := by
  intro a ha
  simp only [sharpCore, List.mem_cons, List.mem_replicate] at ha
  rcases ha with h | ⟨_, h⟩ <;> omega

lemma sharpCore_free (m : ℕ) (hm : 1 ≤ m) : NoScheduleWithFreeDay (sharpCore m) := by
  intro σ d hd
  have h := PinwheelDensity.ExactRange.lemma_2_2 (sharpCore m) (sharpCore_pos m hm) σ d hd
  have hl : (sharpCore m).length = m := by simp [sharpCore]; omega
  have hs : (sharpCore m).sum = m + (m - 1) * (m + 1) := by simp [sharpCore]
  rw [hl, hs] at h
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  simp at h
  nlinarith

lemma density_append (A B : List ℕ) : density (A ++ B) = density A + density B := by
  unfold density; simp [List.bind_eq_flatMap]

lemma density_cons (a : ℕ) (A : List ℕ) : density (a :: A) = 1 / (a : ℚ) + density A := by
  unfold density; simp [List.bind_eq_flatMap]

lemma density_nil : density [] = 0 := by unfold density; rfl

lemma density_replicate (r a : ℕ) : density (List.replicate r a) = (r : ℚ) * (1 / (a : ℚ)) := by
  induction r with
  | zero => simp [density_nil]
  | succ r ih => rw [List.replicate_succ, density_cons, ih]; push_cast; ring

lemma sharpCore_density (m x : ℕ) (hm : 1 ≤ m) (hx : 1 ≤ x) :
    density (sharpCore m ++ [x]) = c m + 1 / (x : ℚ) := by
  have hm' : (1 : ℚ) ≤ m := by exact_mod_cast hm
  have h1 : ((m - 1 : ℕ) : ℚ) = (m : ℚ) - 1 := by push_cast [Nat.cast_sub hm]; ring
  have e : sharpCore m ++ [x] = m :: (List.replicate (m - 1) (m + 1) ++ [x]) := rfl
  rw [e, density_cons, density_append, density_replicate, density_cons, density_nil, h1]
  unfold c
  have : (m : ℚ) + 1 ≠ 0 := by positivity
  have : (m : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

lemma density_nonneg (A : List ℕ) : 0 ≤ density A := by
  induction A with
  | nil => simp [density_nil]
  | cons a t ih => rw [density_cons]; have : (0 : ℚ) ≤ 1 / (a : ℚ) := by positivity
                   linarith

lemma zero_mem (m : ℕ) (hm : 1 ≤ m) : (0 : ℝ) ∈ ThresholdSet m := by
  intro A hA hd
  have : A = [] := by
    rcases A with _ | ⟨a, t⟩
    · rfl
    · exfalso
      have ha := (hA a (by simp)).1
      have : (0 : ℚ) < density (a :: t) := by
        rw [density_cons]
        have h1 : (0 : ℚ) < 1 / (a : ℚ) := by
          have : (0 : ℚ) < a := by exact_mod_cast ha
          positivity
        linarith [density_nonneg t]
      have : ((0 : ℚ) : ℝ) < ((density (a :: t) : ℚ) : ℝ) := by exact_mod_cast this
      simp at this hd
      linarith
  subst this
  exact ⟨fun _ => none, fun i => i.elim0⟩

lemma le_of_mem (m : ℕ) (hm : 1 ≤ m) (δ : ℝ) (hδ : δ ∈ ThresholdSet m) : δ ≤ ((c m : ℚ) : ℝ) := by
  by_contra hlt
  rw [not_le] at hlt
  set ε : ℝ := δ - ((c m : ℚ) : ℝ) with hε
  have hεpos : 0 < ε := by linarith
  obtain ⟨x, hx⟩ := exists_nat_gt (1 / ε + m)
  have hx1 : 1 ≤ x := by
    have : (0 : ℝ) < 1 / ε := by positivity
    have : (0 : ℝ) < x := by have : (0:ℝ) ≤ m := by positivity
                             linarith
    exact_mod_cast this
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hx1
  have hinv : 1 / (x : ℝ) ≤ ε := by
    rw [div_le_iff₀ hxpos]
    have hm0 : (0:ℝ) ≤ m := by positivity
    have : 1 / ε < x := by linarith
    rw [div_lt_iff₀ hεpos] at this
    linarith
  have hsched := hδ (sharpCore m ++ [x]) (by
    intro a ha
    refine ⟨?_, ?_⟩
    · rcases List.mem_append.1 ha with h | h
      · exact sharpCore_pos m hm a h
      · simp at h; omega
    · rcases List.mem_append.1 ha with h | h
      · simp only [sharpCore, List.mem_cons, List.mem_replicate] at h
        rcases h with h | ⟨_, h⟩ <;> omega
      · simp at h
        rw [h]
        have : (m : ℝ) < x := by
          have hεp : (0:ℝ) < 1 / ε := by positivity
          linarith
        exact_mod_cast this.le) (by
    rw [sharpCore_density m x hm hx1]
    push_cast
    linarith)
  exact notSched _ (sharpCore_pos m hm) (sharpCore_free m hm) x hx1 hsched

end PinwheelDensity.ExactRange.Dev.P23

namespace PinwheelDensity.ExactRange

open Dev.P23 in
theorem chk_prop_2_3 (m : ℕ) (hm : 1 ≤ m) :
    (∀ x : ℕ, 1 ≤ x → ¬ Schedulable (sharpCore m ++ [x]) ∧
      density (sharpCore m ++ [x]) = c m + 1 / (x : ℚ)) ∧
    G m ≤ ((c m : ℚ) : ℝ) := by
  refine ⟨fun x hx => ⟨notSched _ (sharpCore_pos m hm) (sharpCore_free m hm) x hx,
    sharpCore_density m x hm hx⟩, ?_⟩
  exact csSup_le ⟨0, zero_mem m hm⟩ (fun δ hδ => le_of_mem m hm δ hδ)

end PinwheelDensity.ExactRange
end

theorem solution : type_of% @PinwheelDensity.ExactRange.chk_prop_2_3 := @PinwheelDensity.ExactRange.chk_prop_2_3
