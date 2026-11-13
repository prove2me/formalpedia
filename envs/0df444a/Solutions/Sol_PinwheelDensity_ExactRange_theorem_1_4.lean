-- Prove2me | solution 1 for PinwheelDensity.ExactRange.theorem_1_4
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T08:27:54.803001+00:00
-- url     : https://prove2.me/submissions/cd6825ec-576f-4813-b63f-147e5e5b07a6

import Mathlib
import Definitions.Def_PinwheelDensity_ExactRange_Schedulable
import Definitions.Def_PinwheelDensity_ExactRange_coreP
import Theorems.Thm_PinwheelDensity_ExactRange_lemma_2_1
import Theorems.Thm_PinwheelDensity_ExactRange_lemma_A_1
import Theorems.Thm_PinwheelDensity_ExactRange_lemma_2_4
import Theorems.Thm_PinwheelDensity_ExactRange_lemma_2_6
section
set_option autoImplicit false

namespace PinwheelDensity.ExactRange.Dev.T14

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

lemma density_append (A B : List ℕ) : density (A ++ B) = density A + density B := by
  unfold density; simp [List.bind_eq_flatMap]

lemma density_cons (a : ℕ) (A : List ℕ) : density (a :: A) = 1 / (a : ℚ) + density A := by
  unfold density; simp [List.bind_eq_flatMap]

lemma density_nil : density [] = 0 := by unfold density; rfl

lemma density_replicate (r a : ℕ) : density (List.replicate r a) = (r : ℚ) * (1 / (a : ℚ)) := by
  induction r with
  | zero => simp [density_nil]
  | succ r ih => rw [List.replicate_succ, density_cons, ih]; push_cast; ring

lemma density_nonneg (A : List ℕ) : 0 ≤ density A := by
  induction A with
  | nil => simp [density_nil]
  | cons a t ih => rw [density_cons]; have : (0 : ℚ) ≤ 1 / (a : ℚ) := by positivity
                   linarith

lemma zero_mem (m : ℕ) : (0 : ℝ) ∈ ThresholdSet m := by
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

/-- Generic upper bound: a free-day-free core with all periods at least `m` bounds `G m`. -/
lemma G_le (m : ℕ) (hm : 1 ≤ m) (P : List ℕ) (hP : ∀ a ∈ P, m ≤ a)
    (hfree : NoScheduleWithFreeDay P) : G m ≤ ((density P : ℚ) : ℝ) := by
  refine csSup_le ⟨0, zero_mem m⟩ (fun δ hδ => ?_)
  by_contra hlt
  rw [not_le] at hlt
  set ε : ℝ := δ - ((density P : ℚ) : ℝ) with hε
  have hεpos : 0 < ε := by linarith
  obtain ⟨x, hx⟩ := exists_nat_gt (1 / ε + m)
  have hm0 : (0:ℝ) ≤ m := by positivity
  have hεp : (0:ℝ) < 1 / ε := by positivity
  have hx1 : 1 ≤ x := by
    have : (0 : ℝ) < x := by linarith
    exact_mod_cast this
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hx1
  have hinv : 1 / (x : ℝ) ≤ ε := by
    rw [div_le_iff₀ hxpos]
    have : 1 / ε < x := by linarith
    rw [div_lt_iff₀ hεpos] at this
    linarith
  have hP1 : ∀ a ∈ P, 1 ≤ a := fun a ha => le_trans hm (hP a ha)
  have hsched := hδ (P ++ [x]) (by
    intro a ha
    refine ⟨?_, ?_⟩
    · rcases List.mem_append.1 ha with h | h
      · exact hP1 a h
      · simp at h; omega
    · rcases List.mem_append.1 ha with h | h
      · exact hP a h
      · simp at h
        rw [h]
        have : (m : ℝ) < x := by linarith
        exact_mod_cast this.le) (by
    rw [density_append, density_cons, density_nil]
    push_cast
    linarith)
  exact notSched _ hP1 hfree x hx1 hsched

lemma coreP_eq' (m : ℕ) (hm : 3 ≤ m) :
    coreP (m + 1) = m :: (List.replicate (m - 2) (m + 1) ++ [2 * m + 1, 4 * m + 3, 5 * m + 5]) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
  have e1 : k + 3 + 1 - 1 = k + 3 := by omega
  have e2 : k + 3 + 1 - 3 = k + 3 - 2 := by omega
  have e3 : 2 * (k + 3 + 1) - 1 = 2 * (k + 3) + 1 := by omega
  have e4 : 4 * (k + 3 + 1) - 1 = 4 * (k + 3) + 3 := by omega
  have e5 : 5 * (k + 3 + 1) = 5 * (k + 3) + 5 := by omega
  simp only [coreP, e1, e2, e3, e4, e5]
  simp

lemma coreP_eq (m x : ℕ) (hm : 3 ≤ m) : coreP (m + 1) ++ [x] = refutationP m x := by
  rw [coreP_eq' m hm]
  simp [refutationP]

lemma coreP_density (m : ℕ) (hm : 3 ≤ m) :
    density (coreP (m + 1)) = 1 / (m : ℚ) + ((m : ℚ) - 2) / ((m : ℚ) + 1) +
      1 / (2 * (m : ℚ) + 1) + 1 / (4 * (m : ℚ) + 3) + 1 / (5 * (m : ℚ) + 5) := by
  have hc : ((m - 2 : ℕ) : ℚ) = (m : ℚ) - 2 := by
    rw [Nat.cast_sub (by omega)]; norm_num
  rw [coreP_eq' m hm, density_cons, density_append, density_replicate, hc]
  simp only [density_cons, density_nil]
  push_cast
  ring

lemma coreP_density_eq (m : ℕ) (hm : 6 ≤ m) : density (coreP (m + 1)) = c m - g m := by
  rw [coreP_density m (by omega)]
  unfold c g
  simp only []
  have hm' : (6 : ℚ) ≤ m := by exact_mod_cast hm
  have e6 : 2 * ((m : ℚ) + 1) - 1 = 2 * m + 1 := by ring
  have e7 : 4 * ((m : ℚ) + 1) - 1 = 4 * m + 3 := by ring
  rw [e6, e7]
  have h1 : (m : ℚ) ≠ 0 := by positivity
  have h2 : (m : ℚ) + 1 ≠ 0 := by positivity
  have h3 : 2 * (m : ℚ) + 1 ≠ 0 := by positivity
  have h4 : 4 * (m : ℚ) + 3 ≠ 0 := by positivity
  have h5 : 5 * (m : ℚ) + 5 ≠ 0 := by positivity
  field_simp
  ring

lemma g_pos (m : ℕ) (hm : 6 ≤ m) : 0 < g m := by
  have hm' : (6 : ℚ) ≤ m := by exact_mod_cast hm
  unfold g
  simp only []
  apply div_pos
  · nlinarith
  · have : 0 < 2 * ((m : ℚ) + 1) - 1 := by linarith
    have : 0 < 4 * ((m : ℚ) + 1) - 1 := by linarith
    positivity

lemma g_le (m : ℕ) (hm : 6 ≤ m) : g m ≤ 1 / (m : ℚ) := by
  have hm' : (6 : ℚ) ≤ m := by exact_mod_cast hm
  unfold g
  simp only []
  have h1 : 0 < 2 * ((m : ℚ) + 1) - 1 := by linarith
  have h2 : 0 < 4 * ((m : ℚ) + 1) - 1 := by linarith
  have h3 : 0 < 5 * ((m : ℚ) + 1) * (2 * ((m : ℚ) + 1) - 1) * (4 * ((m : ℚ) + 1) - 1) := by positivity
  rw [div_le_div_iff₀ h3 (by linarith)]
  nlinarith [mul_pos h1 h2, mul_pos (mul_pos h1 h2) (by linarith : (0:ℚ) < m)]

lemma coreQ_eq (m : ℕ) (hm : 4 ≤ m) :
    coreQ m = m :: m :: (List.replicate (m - 3) (m + 1) ++ [2 * m + 2, 3 * m + 2]) := by
  simp [coreQ]

lemma coreQ_density (m : ℕ) (hm : 4 ≤ m) :
    density (coreQ m) = 2 / (m : ℚ) + ((m : ℚ) - 3) / ((m : ℚ) + 1) + 1 / (2 * (m : ℚ) + 2) +
          1 / (3 * (m : ℚ) + 2) := by
  have hc : ((m - 3 : ℕ) : ℚ) = (m : ℚ) - 3 := by
    rw [Nat.cast_sub (by omega)]; norm_num
  rw [coreQ_eq m hm, density_cons, density_cons, density_append, density_replicate, hc]
  simp only [density_cons, density_nil]
  push_cast
  ring

lemma coreQ_density' (m : ℕ) (hm : 4 ≤ m) :
    density (coreQ m) = 1 - (7 * (m : ℚ) ^ 2 - 8 * (m : ℚ) - 8) /
          (2 * (m : ℚ) * (3 * (m : ℚ) ^ 2 + 5 * (m : ℚ) + 2)) := by
  rw [coreQ_density m hm]
  have hm' : (4 : ℚ) ≤ m := by exact_mod_cast hm
  have h1 : (m : ℚ) ≠ 0 := by positivity
  have h2 : (m : ℚ) + 1 ≠ 0 := by positivity
  have h3 : 2 * (m : ℚ) + 2 ≠ 0 := by positivity
  have h4 : 3 * (m : ℚ) + 2 ≠ 0 := by positivity
  have h5 : 3 * (m : ℚ) ^ 2 + 5 * (m : ℚ) + 2 ≠ 0 := by positivity
  field_simp
  ring

lemma q_pos (m : ℕ) (hm : 7 ≤ m) : 0 < qThreshold m := by
  have hm' : (7 : ℚ) ≤ m := by exact_mod_cast hm
  unfold qThreshold
  apply div_pos
  · positivity
  · nlinarith

lemma c_sub_Q (m : ℕ) (hm : 7 ≤ m) : c m - density (coreQ m) = 1 / qThreshold m := by
  rw [coreQ_density m (by omega)]
  have hm' : (7 : ℚ) ≤ m := by exact_mod_cast hm
  have hq := q_pos m hm
  unfold c
  unfold qThreshold at hq ⊢
  have h1 : (m : ℚ) ≠ 0 := by positivity
  have h2 : (m : ℚ) + 1 ≠ 0 := by positivity
  have h3 : 2 * (m : ℚ) + 2 ≠ 0 := by positivity
  have h4 : 3 * (m : ℚ) + 2 ≠ 0 := by positivity
  have h5 : (m : ℚ) ^ 2 - 6 * (m : ℚ) - 4 ≠ 0 := by intro h; rw [h] at hq; simp at hq
  field_simp
  ring

lemma Q_lt (m : ℕ) (hm : 7 ≤ m) : density (coreQ m) < c m - g m := by
  have h := c_sub_Q m hm
  have hq := q_pos m hm
  have hm' : (7 : ℚ) ≤ m := by exact_mod_cast hm
  have : g m < 1 / qThreshold m := by
    unfold g qThreshold
    simp only []
    obtain ⟨t, ht⟩ : ∃ t : ℚ, 0 ≤ t ∧ (m : ℚ) = t + 7 := ⟨(m : ℚ) - 7, by linarith, by ring⟩
    rw [ht.2]
    have e6 : 2 * ((t + 7 + 1 : ℚ)) - 1 = 2 * t + 15 := by ring
    have e7 : 4 * ((t + 7 + 1 : ℚ)) - 1 = 4 * t + 31 := by ring
    rw [e6, e7]
    have ht0 := ht.1
    rw [one_div, inv_div, div_lt_div_iff₀ (by positivity) (by positivity)]
    rw [← sub_pos]
    ring_nf
    positivity
  linarith

lemma qThreshold_ge (m : ℕ) (hm : 7 ≤ m) : (m : ℚ) ≤ qThreshold m := by
  have hm' : (7 : ℚ) ≤ m := by exact_mod_cast hm
  unfold qThreshold
  rw [le_div_iff₀ (by nlinarith)]
  nlinarith [mul_pos (by linarith : (0:ℚ) < m) (by linarith : (0:ℚ) < m)]

lemma coreP_ge (m : ℕ) (hm : 3 ≤ m) : ∀ a ∈ coreP (m + 1), m ≤ a := by
  intro a ha
  rw [coreP_eq' m hm] at ha
  simp [List.mem_replicate] at ha
  omega

lemma coreQ_ge (m : ℕ) (hm : 4 ≤ m) : ∀ a ∈ coreQ m, m ≤ a := by
  intro a ha
  rw [coreQ_eq m hm] at ha
  simp [List.mem_replicate] at ha
  omega

lemma refutation_density (m x : ℕ) (hm : 6 ≤ m) :
    density (refutationP m x) = c m - g m + 1 / (x : ℚ) := by
  rw [← coreP_eq m x (by omega), density_append, coreP_density_eq m hm, density_cons, density_nil]
  ring

lemma refutation_le_iff (m x : ℕ) (hm : 6 ≤ m) (hx : 1 ≤ x) :
    density (refutationP m x) ≤ c m ↔ 1 ≤ (x : ℚ) * g m := by
  rw [refutation_density m x hm]
  have hx' : (0 : ℚ) < x := by exact_mod_cast hx
  have : 1 / (x : ℚ) ≤ g m ↔ 1 ≤ (x : ℚ) * g m := by
    rw [div_le_iff₀ hx']; constructor <;> intro h <;> linarith
  rw [← this]; constructor <;> intro h <;> linarith

lemma part1 (m : ℕ) (hm : 6 ≤ m) :
    (∃ A : List ℕ, (∀ a ∈ A, 1 ≤ a) ∧ IsMinPeriod m A ∧ density A ≤ c m ∧ ¬ Schedulable A) ∧
      0 < g m ∧
      (∀ x : ℕ, 1 ≤ x → ¬ Schedulable (refutationP m x)) ∧
      (∀ x : ℕ, ⌈1 / g m⌉₊ ≤ x →
        IsMinPeriod m (refutationP m x) ∧ density (refutationP m x) ≤ c m) ∧
      G m ≤ ((c m - g m : ℚ) : ℝ) ∧ c m - g m < c m := by
  have hg := g_pos m hm
  have hfree := (lemma_2_4 (m + 1) (by omega)).1
  have hge := coreP_ge m (by omega)
  have hpos : ∀ a ∈ coreP (m + 1), 1 ≤ a := fun a ha => le_trans (by omega) (hge a ha)
  have hm0 : (0 : ℚ) < m := by have : (6:ℚ) ≤ m := by exact_mod_cast hm
                               linarith
  have hunsched : ∀ x : ℕ, 1 ≤ x → ¬ Schedulable (refutationP m x) := by
    intro x hx
    rw [← coreP_eq m x (by omega)]
    exact notSched _ hpos hfree x hx
  have hd : ∀ x : ℕ, ⌈1 / g m⌉₊ ≤ x →
      IsMinPeriod m (refutationP m x) ∧ density (refutationP m x) ≤ c m := by
    intro x hx
    have h1 : 1 / g m ≤ (x : ℚ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hx)
    have h2 : (m : ℚ) ≤ 1 / g m := by
      rw [le_div_iff₀ hg]
      have := g_le m hm
      rw [le_div_iff₀ hm0] at this
      linarith
    have hmx : m ≤ x := by exact_mod_cast le_trans h2 h1
    have hx1 : 1 ≤ x := by omega
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simp [refutationP]
    · intro a ha
      rw [← coreP_eq m x (by omega)] at ha
      rcases List.mem_append.1 ha with h | h
      · exact hge a h
      · simp at h; omega
    · rw [refutation_le_iff m x hm hx1]
      rw [div_le_iff₀ hg] at h1
      exact h1
  have hceil : 1 ≤ ⌈1 / g m⌉₊ := by
    have : (m : ℚ) ≤ 1 / g m := by
      rw [le_div_iff₀ hg]
      have := g_le m hm
      rw [le_div_iff₀ hm0] at this
      linarith
    have h6 : (0 : ℚ) < 1 / g m := by positivity
    exact Nat.ceil_pos.2 h6
  refine ⟨⟨refutationP m ⌈1 / g m⌉₊, ?_, (hd _ le_rfl).1, (hd _ le_rfl).2,
    hunsched _ hceil⟩, hg, hunsched, hd, ?_, by linarith⟩
  · intro a ha
    rw [← coreP_eq m _ (by omega)] at ha
    rcases List.mem_append.1 ha with h | h
    · exact hpos a h
    · rw [List.mem_singleton] at h; omega
  · have := G_le m (by omega) (coreP (m + 1)) hge hfree
    rw [coreP_density_eq m hm] at this
    exact this

lemma part2 :
    (⌈1 / g 6⌉₊ = 3072 ∧
      IsLeast {x : ℕ | 1 ≤ x ∧ density (refutationP 6 x) ≤ c 6} 3072 ∧
      refutationP 6 3072 = [6, 7, 7, 7, 7, 13, 27, 35, 3072]) := by
  have hg : g 6 = 4 / 12285 := by unfold g; norm_num
  refine ⟨?_, ⟨⟨by norm_num, ?_⟩, ?_⟩, by decide⟩
  · rw [hg, Nat.ceil_eq_iff (by norm_num)]
    norm_num
  · rw [refutation_le_iff 6 3072 (by norm_num) (by norm_num), hg]
    norm_num
  · rintro x ⟨hx, hd⟩
    rw [refutation_le_iff 6 x (by norm_num) hx, hg] at hd
    by_contra hlt
    rw [not_le] at hlt
    have : (x : ℚ) ≤ 3071 := by exact_mod_cast (by omega : x ≤ 3071)
    linarith

lemma part3 (m : ℕ) (hm : 7 ≤ m) :
      (∀ x : ℕ, 1 ≤ x → ¬ Schedulable (coreQ m ++ [x])) ∧
      density (coreQ m) =
        2 / (m : ℚ) + ((m : ℚ) - 3) / ((m : ℚ) + 1) + 1 / (2 * (m : ℚ) + 2) +
          1 / (3 * (m : ℚ) + 2) ∧
      density (coreQ m) =
        1 - (7 * (m : ℚ) ^ 2 - 8 * (m : ℚ) - 8) /
          (2 * (m : ℚ) * (3 * (m : ℚ) ^ 2 + 5 * (m : ℚ) + 2)) ∧
      density (coreQ m) < c m - g m ∧
      G m ≤ ((density (coreQ m) : ℚ) : ℝ) ∧
      c m - g m < c m ∧
      1 - ((density (coreQ m) : ℚ) : ℝ) ≤ 1 - G m ∧
      (∀ x : ℕ, ⌈qThreshold m⌉₊ ≤ x →
        IsMinPeriod m (coreQ m ++ [x]) ∧ density (coreQ m ++ [x]) ≤ c m) := by
  have hfree := (lemma_2_6 m (by omega)).1
  have hge := coreQ_ge m (by omega)
  have hpos : ∀ a ∈ coreQ m, 1 ≤ a := fun a ha => le_trans (by omega) (hge a ha)
  have hG := G_le m (by omega) (coreQ m) hge hfree
  have hg := g_pos m (by omega)
  have hq := q_pos m hm
  refine ⟨fun x hx => notSched _ hpos hfree x hx, coreQ_density m (by omega),
    coreQ_density' m (by omega), Q_lt m hm, hG, by linarith, by linarith, ?_⟩
  intro x hx
  have h1 : qThreshold m ≤ (x : ℚ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hx)
  have h2 := qThreshold_ge m hm
  have hmx : m ≤ x := by exact_mod_cast le_trans h2 h1
  have hx0 : (0 : ℚ) < x := by linarith
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [coreQ_eq m (by omega)]; simp
  · intro a ha
    rcases List.mem_append.1 ha with h | h
    · exact hge a h
    · simp at h; omega
  · rw [density_append, density_cons, density_nil]
    have := c_sub_Q m hm
    have h3 : 1 / (x : ℚ) ≤ 1 / qThreshold m := one_div_le_one_div_of_le hq h1
    linarith

lemma part4 : ∃ (C : ℝ) (M : ℕ), ∀ m : ℕ, M ≤ m →
      |(1 - ((density (coreQ m) : ℚ) : ℝ)) - (7 / (6 * (m : ℝ)) - 59 / (18 * (m : ℝ) ^ 2))| ≤
        C / (m : ℝ) ^ 3 := by
  refine ⟨6, 7, fun m hm => ?_⟩
  have hm' : (7 : ℝ) ≤ m := by exact_mod_cast hm
  have hd := congrArg ((↑) : ℚ → ℝ) (coreQ_density' m (by omega))
  push_cast at hd
  rw [hd]
  have h1 : (m : ℝ) ≠ 0 := by positivity
  have h5 : 3 * (m : ℝ) ^ 2 + 5 * (m : ℝ) + 2 ≠ 0 := by positivity
  have e : 1 - (1 - (7 * (m : ℝ) ^ 2 - 8 * (m : ℝ) - 8) /
        (2 * (m : ℝ) * (3 * (m : ℝ) ^ 2 + 5 * (m : ℝ) + 2))) -
      (7 / (6 * (m : ℝ)) - 59 / (18 * (m : ℝ) ^ 2)) =
      (181 * m + 118) / (18 * (m : ℝ) ^ 2 * (3 * (m : ℝ) ^ 2 + 5 * (m : ℝ) + 2)) := by
    field_simp
    ring
  rw [e, abs_of_nonneg (by positivity)]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_pos (by linarith : (0:ℝ) < m) (by linarith : (0:ℝ) < m),
    pow_pos (by linarith : (0:ℝ) < m) 3, pow_pos (by linarith : (0:ℝ) < m) 4,
    pow_pos (by linarith : (0:ℝ) < m) 5]

lemma part5 : ⌈qThreshold 7⌉₊ = 859 ∧ coreQ 7 ++ [859] = [7, 7, 8, 8, 8, 8, 16, 23, 859] := by
  refine ⟨?_, by decide⟩
  have : qThreshold 7 = 2576 / 3 := by unfold qThreshold; norm_num
  rw [this, Nat.ceil_eq_iff (by norm_num)]
  norm_num

end PinwheelDensity.ExactRange.Dev.T14

namespace PinwheelDensity.ExactRange

open Dev.T14 in
theorem chk_theorem_1_4 :
    (∀ m : ℕ, 6 ≤ m →
      (∃ A : List ℕ, (∀ a ∈ A, 1 ≤ a) ∧ IsMinPeriod m A ∧ density A ≤ c m ∧ ¬ Schedulable A) ∧
      0 < g m ∧
      (∀ x : ℕ, 1 ≤ x → ¬ Schedulable (refutationP m x)) ∧
      (∀ x : ℕ, ⌈1 / g m⌉₊ ≤ x →
        IsMinPeriod m (refutationP m x) ∧ density (refutationP m x) ≤ c m) ∧
      G m ≤ ((c m - g m : ℚ) : ℝ) ∧ c m - g m < c m) ∧
    (⌈1 / g 6⌉₊ = 3072 ∧
      IsLeast {x : ℕ | 1 ≤ x ∧ density (refutationP 6 x) ≤ c 6} 3072 ∧
      refutationP 6 3072 = [6, 7, 7, 7, 7, 13, 27, 35, 3072]) ∧
    (∀ m : ℕ, 7 ≤ m →
      (∀ x : ℕ, 1 ≤ x → ¬ Schedulable (coreQ m ++ [x])) ∧
      density (coreQ m) =
        2 / (m : ℚ) + ((m : ℚ) - 3) / ((m : ℚ) + 1) + 1 / (2 * (m : ℚ) + 2) +
          1 / (3 * (m : ℚ) + 2) ∧
      density (coreQ m) =
        1 - (7 * (m : ℚ) ^ 2 - 8 * (m : ℚ) - 8) /
          (2 * (m : ℚ) * (3 * (m : ℚ) ^ 2 + 5 * (m : ℚ) + 2)) ∧
      density (coreQ m) < c m - g m ∧
      G m ≤ ((density (coreQ m) : ℚ) : ℝ) ∧
      c m - g m < c m ∧
      1 - ((density (coreQ m) : ℚ) : ℝ) ≤ 1 - G m ∧
      (∀ x : ℕ, ⌈qThreshold m⌉₊ ≤ x →
        IsMinPeriod m (coreQ m ++ [x]) ∧ density (coreQ m ++ [x]) ≤ c m)) ∧
    (∃ (C : ℝ) (M : ℕ), ∀ m : ℕ, M ≤ m →
      |(1 - ((density (coreQ m) : ℚ) : ℝ)) - (7 / (6 * (m : ℝ)) - 59 / (18 * (m : ℝ) ^ 2))| ≤
        C / (m : ℝ) ^ 3) ∧
    (⌈qThreshold 7⌉₊ = 859 ∧ coreQ 7 ++ [859] = [7, 7, 8, 8, 8, 8, 16, 23, 859]) :=
  ⟨part1, part2, part3, part4, part5⟩

end PinwheelDensity.ExactRange
end

theorem solution : type_of% @PinwheelDensity.ExactRange.chk_theorem_1_4 := @PinwheelDensity.ExactRange.chk_theorem_1_4
