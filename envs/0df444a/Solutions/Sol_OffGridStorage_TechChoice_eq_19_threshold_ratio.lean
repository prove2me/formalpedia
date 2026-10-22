-- Prove2me | solution 1 for OffGridStorage.TechChoice.eq_19_threshold_ratio
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:04:16.038975+00:00
-- url     : https://prove2.me/submissions/22248118-2b6d-4b56-bb22-5f531932e5a2

import Mathlib
import Definitions.Def_OffGridStorage_TechChoice_Model
set_option autoImplicit false

open OffGridStorage.TechChoice

lemma uu_g0_strictMono (cQ : ℝ) (hcQ : 0 < cQ) {r r' : ℝ} (h0 : 0 ≤ r) (h : r < r') :
    g0ratio cQ r < g0ratio cQ r' := by
  unfold g0ratio
  have : Real.sqrt (cQ ^ 2 + 2 * cQ * r) < Real.sqrt (cQ ^ 2 + 2 * cQ * r') := by
    apply Real.sqrt_lt_sqrt (by positivity)
    nlinarith
  linarith

lemma uu_g0_at (cQ g : ℝ) (hcQ : 0 < cQ) (hg : 2 * cQ < g) :
    0 ≤ g - Real.sqrt (2 * cQ * g) ∧ g0ratio cQ (g - Real.sqrt (2 * cQ * g)) = g := by
  have hs0 : 0 ≤ Real.sqrt (2 * cQ * g) := Real.sqrt_nonneg _
  have hsq : Real.sqrt (2 * cQ * g) ^ 2 = 2 * cQ * g := Real.sq_sqrt (by nlinarith)
  have hle : Real.sqrt (2 * cQ * g) ≤ g := by
    apply Real.sqrt_le_iff.2
    refine ⟨by linarith, ?_⟩
    nlinarith
  refine ⟨by linarith, ?_⟩
  unfold g0ratio
  set s := Real.sqrt (2 * cQ * g) with hs
  have key : cQ ^ 2 + 2 * cQ * (g - s) = (s - cQ) ^ 2 := by nlinarith
  rw [key, Real.sqrt_sq]
  · ring
  · -- s ≥ cQ since s^2 = 2 cQ g > 4 cQ^2
    nlinarith

theorem solution (cQ r g : ℝ) (hcQ : 0 < cQ) (hr : 0 ≤ r) (hg : 2 * cQ < g) :
    (g0ratio cQ r = g ↔ r = g - Real.sqrt (2 * cQ * g)) ∧
    (g0ratio cQ r < g ↔ r < g - Real.sqrt (2 * cQ * g)) := by
  obtain ⟨h0, hat⟩ := uu_g0_at cQ g hcQ hg
  set r0 := g - Real.sqrt (2 * cQ * g)
  constructor
  · constructor
    · intro h
      rcases lt_trichotomy r r0 with hlt | heq | hgt
      · have := uu_g0_strictMono cQ hcQ hr hlt; rw [hat] at this; linarith
      · exact heq
      · have := uu_g0_strictMono cQ hcQ h0 hgt; rw [hat] at this; linarith
    · intro h; rw [h]; exact hat
  · constructor
    · intro h
      by_contra hn
      push_neg at hn
      rcases eq_or_lt_of_le hn with heq | hgt
      · rw [← heq] at h; rw [hat] at h; exact lt_irrefl _ h
      · have := uu_g0_strictMono cQ hcQ h0 hgt; rw [hat] at this; linarith
    · intro h
      have := uu_g0_strictMono cQ hcQ hr h
      rw [hat] at this; exact this
