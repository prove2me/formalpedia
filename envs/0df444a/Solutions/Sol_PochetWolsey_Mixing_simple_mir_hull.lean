-- Prove2me | solution 1 for PochetWolsey.Mixing.simple_mir_hull
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T04:17:33.792998+00:00
-- url     : https://prove2.me/submissions/ede58c25-f10b-4356-a67e-3a9c95c88791

import Mathlib
import Definitions.Def_PochetWolsey_Mixing_Model

open PochetWolsey.Mixing

theorem solution (b : ℝ) :
    (∀ p ∈ basicSet b, frac b * ((⌈b⌉ : ℝ) - p.2) ≤ p.1) ∧
    convexHull ℝ (basicSet b) =
      {p : ℝ × ℝ | b ≤ p.1 + p.2 ∧
        frac b * (⌈b⌉ : ℝ) ≤ p.1 + frac b * p.2 ∧ 0 ≤ p.1} := by
  have hf0 : 0 ≤ frac b := by unfold frac; linarith [Int.floor_le b]
  have hf1 : frac b < 1 := by unfold frac; linarith [Int.lt_floor_add_one b]
  have hfb : frac b = b - ⌊b⌋ := rfl
  have hceil : (⌈b⌉ : ℝ) ≤ ⌊b⌋ + 1 := by exact_mod_cast Int.ceil_le_floor_add_one b
  have hceil2 : b ≤ (⌈b⌉ : ℝ) := Int.le_ceil b
  have hfc : frac b * (⌈b⌉ : ℝ) = frac b * (⌊b⌋ + 1) := by
    rcases eq_or_ne (frac b) 0 with h | h
    · rw [h]; ring
    · congr 1
      have hlt : (⌊b⌋ : ℝ) < b := by
        rcases lt_or_eq_of_le (Int.floor_le b) with h' | h'
        · exact h'
        · exact absurd (by rw [hfb, h']; ring) h
      have : ⌈b⌉ = ⌊b⌋ + 1 := by
        rw [Int.ceil_eq_iff]; push_cast
        exact ⟨by linarith, (Int.lt_floor_add_one b).le⟩
      rw [this]; push_cast; ring
  have part1 : ∀ p ∈ basicSet b, frac b * ((⌈b⌉ : ℝ) - p.2) ≤ p.1 := by
    rintro ⟨s, y⟩ ⟨hs, ⟨z, hz⟩, hsy⟩
    simp only at hs hz hsy ⊢
    subst hz
    by_cases hzc : ⌈b⌉ ≤ z
    · have : (⌈b⌉ : ℝ) ≤ z := by exact_mod_cast hzc
      nlinarith
    · have hz' : z ≤ ⌊b⌋ := by
        have := Int.ceil_le_floor_add_one b; omega
      have hz'' : (z : ℝ) ≤ ⌊b⌋ := by exact_mod_cast hz'
      rw [mul_sub, hfc]
      nlinarith
  refine ⟨part1, ?_⟩
  apply Set.Subset.antisymm
  · apply convexHull_min
    · intro p hp
      have h1 := part1 p hp
      obtain ⟨hs, _, hsy⟩ := hp
      refine ⟨hsy, by linarith, hs⟩
    · intro p hp q hq a c ha hc hac
      obtain ⟨p1, p2, p3⟩ := hp
      obtain ⟨q1, q2, q3⟩ := hq
      simp only [Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        smul_eq_mul]
      refine ⟨?_, ?_, ?_⟩
      · have : b = a * b + c * b := by rw [← add_mul, hac, one_mul]
        nlinarith
      · have : frac b * ⌈b⌉ = a * (frac b * ⌈b⌉) + c * (frac b * ⌈b⌉) := by
          rw [← add_mul, hac, one_mul]
        nlinarith
      · nlinarith
  · rintro ⟨s, y⟩ ⟨hsy, hmir, hs⟩
    simp only at hsy hmir hs
    set k := ⌊y⌋ with hk
    set θ := y - k with hθ
    have hθ0 : 0 ≤ θ := by rw [hθ]; linarith [Int.floor_le y]
    have hθ1 : θ < 1 := by rw [hθ]; linarith [Int.lt_floor_add_one y]
    -- find c with the two endpoints in the basic set
    obtain ⟨c, hc1, hc2⟩ : ∃ c : ℝ, (s + θ * c, (k : ℝ)) ∈ basicSet b ∧
        (s - (1 - θ) * c, ((k + 1 : ℤ) : ℝ)) ∈ basicSet b := by
      set m := ⌊b⌋ with hm
      have hbm : (m : ℝ) ≤ b := Int.floor_le b
      have hbm1 : b < m + 1 := Int.lt_floor_add_one b
      rcases lt_trichotomy k m with hkm | hkm | hkm
      · have hkm' : (k : ℝ) + 1 ≤ m := by exact_mod_cast hkm
        refine ⟨1, ⟨by nlinarith, ⟨k, rfl⟩, by linarith⟩,
          ⟨by nlinarith, ⟨k + 1, rfl⟩, by push_cast; linarith⟩⟩
      · have hkm' : (k : ℝ) = m := by exact_mod_cast hkm
        rw [hfc] at hmir
        have hy : y = k + θ := by rw [hθ]; ring
        have key : frac b * (1 - θ) ≤ s := by rw [hy, hkm'] at hmir; nlinarith
        refine ⟨frac b, ⟨by nlinarith, ⟨k, rfl⟩, by rw [hfb]; nlinarith⟩,
          ⟨by nlinarith, ⟨k + 1, rfl⟩, by push_cast; rw [hfb] at hf1 ⊢; nlinarith⟩⟩
      · have hkm' : (m : ℝ) + 1 ≤ k := by exact_mod_cast hkm
        refine ⟨0, ⟨by simpa using hs, ⟨k, rfl⟩, by simp; linarith⟩,
          ⟨by simpa using hs, ⟨k + 1, rfl⟩, by push_cast; simp; linarith⟩⟩
    apply segment_subset_convexHull hc1 hc2
    refine ⟨1 - θ, θ, by linarith, hθ0, by ring, ?_⟩
    ext
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]; ring
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]; push_cast; rw [hθ]; ring
