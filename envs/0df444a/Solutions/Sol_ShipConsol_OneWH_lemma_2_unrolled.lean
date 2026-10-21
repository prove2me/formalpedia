-- Prove2me | solution 1 for ShipConsol.OneWH.lemma_2_unrolled
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T14:56:33.571989+00:00
-- url     : https://prove2.me/submissions/f033a76e-81f3-4748-a504-cf48b444b810

import Mathlib
import Definitions.Def_ShipConsol_OneWH_Setting

set_option autoImplicit false
open ShipConsol.OneWH

theorem V_one (F : ℝ → ℝ) (α : ℝ) (d z : ℕ) : V F α d 1 z = F z := rfl

theorem Vinf_one (F : ℝ → ℝ) (α : ℝ) (d : ℕ) : Vinf F α d 1 = 0 := rfl

theorem V_succ (F : ℝ → ℝ) (α : ℝ) (d t z : ℕ) :
    V F α d (t + 2) z =
      if z ≤ 1 then F z + Vinf F α d (t + 2)
      else min (F z + Vinf F α d (t + 2)) (V F α d (t + 1) (z - 1)) := rfl

theorem char_V (F : ℝ → ℝ) (α : ℝ) (d : ℕ) : ∀ t : ℕ, 1 ≤ t → ∀ z : ℕ, 1 ≤ z →
    (∀ j, j < min t z → V F α d t z ≤ F ((z - j : ℕ) : ℝ) + Vinf F α d (t - j)) ∧
    ∃ j, j < min t z ∧ V F α d t z = F ((z - j : ℕ) : ℝ) + Vinf F α d (t - j) := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base =>
    intro z hz
    have hm : min 1 z = 1 := by omega
    rw [hm]
    refine ⟨fun j hj => ?_, 0, by omega, ?_⟩
    · have : j = 0 := by omega
      subst this
      simp [V_one, Vinf_one]
    · simp [V_one, Vinf_one]
  | succ t ht ih =>
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    intro z hz
    by_cases hz1 : z ≤ 1
    · have hm : min (s + 1 + 1) z = 1 := by omega
      rw [hm]
      have hV : V F α d (s + 1 + 1) z = F z + Vinf F α d (s + 1 + 1) := by
        rw [show s + 1 + 1 = s + 2 from rfl, V_succ, if_pos hz1]
      refine ⟨fun j hj => ?_, 0, by omega, ?_⟩
      · have : j = 0 := by omega
        subst this
        simp [hV]
      · simp [hV]
    · have hz2 : 2 ≤ z := by omega
      obtain ⟨ihA, j0, hj0, ihB⟩ := ih (z - 1) (by omega)
      have hV : V F α d (s + 1 + 1) z =
          min (F z + Vinf F α d (s + 1 + 1)) (V F α d (s + 1) (z - 1)) := by
        rw [show s + 1 + 1 = s + 2 from rfl, V_succ, if_neg hz1]
      refine ⟨fun j hj => ?_, ?_⟩
      · rw [hV]
        rcases Nat.eq_zero_or_pos j with h0 | hpos
        · subst h0
          simpa using min_le_left _ _
        · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
          have hj' : j' < min (s + 1) (z - 1) := by omega
          refine le_trans (min_le_right _ _) (le_trans (ihA j' hj') ?_)
          have e1 : z - 1 - j' = z - (j' + 1) := by omega
          have e2 : s + 1 - j' = s + 1 + 1 - (j' + 1) := by omega
          rw [e1, e2]
      · rw [hV]
        rcases min_choice (F z + Vinf F α d (s + 1 + 1)) (V F α d (s + 1) (z - 1)) with h | h
        · refine ⟨0, by omega, ?_⟩
          rw [h]; simp
        · refine ⟨j0 + 1, by omega, ?_⟩
          rw [h, ihB]
          have e1 : z - 1 - j0 = z - (j0 + 1) := by omega
          have e2 : s + 1 - j0 = s + 1 + 1 - (j0 + 1) := by omega
          rw [e1, e2]

theorem incr_mono (F : ℝ → ℝ) (hF : ConvexOn ℝ (Set.Ici 1) F) (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) :
    F ((a + 1 : ℕ) : ℝ) - F (a : ℝ) ≤ F ((b + 1 : ℕ) : ℝ) - F (b : ℝ) := by
  induction b, hab using Nat.le_induction with
  | base => exact le_refl _
  | succ b hab ih =>
    refine le_trans ih ?_
    have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast (le_trans ha hab)
    have h := hF.slope_mono_adjacent (x := (b : ℝ)) (y := (b : ℝ) + 1) (z := (b : ℝ) + 1 + 1)
      (by simp only [Set.mem_Ici]; exact hb1) (by simp only [Set.mem_Ici]; linarith)
      (by linarith) (by linarith)
    have e1 : (b : ℝ) + 1 - b = 1 := by ring
    have e2 : (b : ℝ) + 1 + 1 - ((b : ℝ) + 1) = 1 := by ring
    rw [e1, e2, div_one, div_one] at h
    push_cast
    linarith

theorem lemma2_aux (F : ℝ → ℝ) (hFconv : ConvexOn ℝ (Set.Ici 1) F) (α : ℝ) (d t z : ℕ)
    (ht : 1 ≤ t) (hz : 2 ≤ z) :
    V F α d t (z - 1) - V F α d t z ≥ F ((z - 1 : ℕ) : ℝ) - F (z : ℝ) := by
  obtain ⟨-, j, hj, hVj⟩ := char_V F α d t ht (z - 1) (by omega)
  obtain ⟨hA, -⟩ := char_V F α d t ht z (by omega)
  have h1 := hA j (by omega)
  have hmono := incr_mono F hFconv (z - j - 1) (z - 1) (by omega) (by omega)
  have e1 : z - j - 1 + 1 = z - j := by omega
  have e2 : z - 1 - 1 + 1 = z - 1 := by omega
  have e3 : z - 1 + 1 = z := by omega
  have e4 : z - 1 - j = z - j - 1 := by omega
  rw [e1, e3] at hmono
  rw [hVj, e4]
  have e5 : ((z - 1 : ℕ) : ℝ) = ((z - 1 : ℕ) : ℝ) := rfl
  linarith

theorem solution (F : ℝ → ℝ) (hFconv : ConvexOn ℝ (Set.Ici 1) F) (hFanti : AntitoneOn F (Set.Ici 1)) (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (d : ℕ) (hd : 1 ≤ d) (t z : ℕ) (ht : 1 ≤ t) (hz1 : 1 ≤ z) (hzd : z ≤ d) : V F α d t z = (Finset.range (min t z)).inf' (Finset.nonempty_range_iff.mpr (by omega)) (fun j => F ((z - j : ℕ) : ℝ) + Vinf F α d (t - j)) := by
  obtain ⟨hA, j, hj, hVj⟩ := char_V F α d t ht z hz1
  apply le_antisymm
  · rw [Finset.le_inf'_iff]
    intro i hi
    exact hA i (Finset.mem_range.mp hi)
  · rw [hVj]
    exact Finset.inf'_le _ (Finset.mem_range.mpr hj)
