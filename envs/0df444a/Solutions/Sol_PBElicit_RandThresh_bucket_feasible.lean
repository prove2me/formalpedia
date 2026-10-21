-- Prove2me | solution 1 for PBElicit.RandThresh.bucket_feasible
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T07:42:22.226113+00:00
-- url     : https://prove2.me/submissions/feff5912-de5b-4f86-8199-bfe54181537c

import Mathlib
import Definitions.Def_PBElicit_RandThresh_Setting

open Classical PBElicit.RandThresh

lemma pb_mem_bucket {A : Type*} [Fintype A] (c : A → ℝ) (m j : ℕ) (a : A) :
    a ∈ bucket c m j ↔ c a ∈ Ivl m j := by
  simp [bucket]

theorem solution {A : Type*} [Fintype A] (c : A → ℝ) (m K : ℕ)
    (hA : Fintype.card A = m) (hmK : m = 2 ^ K) (j : ℕ) (hj : j ≤ 2 * K) (S : Finset A)
    (hS : S ⊆ bucket c m j) (hcard : (S.card : ℝ) ≤ 1 / up m j) :
    cost c S ≤ 1 := by
  have hmpos : (0:ℝ) < m := by rw [hmK]; positivity
  have hup : 0 < up m j := by unfold up; positivity
  have hle : ∀ a ∈ S, c a ≤ up m j := by
    intro a ha
    have := (pb_mem_bucket c m j a).mp (hS ha)
    simp only [Ivl] at this
    split_ifs at this with h0
    · subst h0; simp only [up, pow_zero]; exact this.2
    · exact this.2
  unfold cost
  have h := Finset.sum_le_card_nsmul S c (up m j) hle
  rw [nsmul_eq_mul] at h
  have : (S.card : ℝ) * up m j ≤ 1 := by
    rw [le_div_iff₀ hup] at hcard; linarith
  linarith
