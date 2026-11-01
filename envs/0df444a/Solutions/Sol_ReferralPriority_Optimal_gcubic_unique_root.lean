-- Prove2me | solution 1 for ReferralPriority.Optimal.gcubic_unique_root
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T12:16:27.988376+00:00
-- url     : https://prove2.me/submissions/9f2e7cad-4e07-420f-9627-2e30787b670f

import Mathlib
import Definitions.Def_ReferralPriority_Optimal_Model

open ReferralPriority.Optimal

theorem solution (E : Env) (hS : E.Standing) (hk : E.k < E.V - E.c / E.mu) :
    ∃ rs ∈ Set.Ioo (0 : ℝ) 1, gcubic E rs = 0 ∧
      (∀ r ∈ Set.Ioo (0 : ℝ) 1, gcubic E r = 0 → r = rs) ∧
      (∀ r ∈ Set.Ioo 0 rs, 0 < gcubic E r) ∧
      (∀ r ∈ Set.Ioo rs 1, gcubic E r < 0) := by
  obtain ⟨hmu, hc, hkpos, hV⟩ := hS
  have hcm : 0 < E.c / E.mu := div_pos hc hmu
  have ha : E.c < (E.V - E.k) * E.mu := by
    have : E.c / E.mu < E.V - E.k := by linarith
    rwa [div_lt_iff₀ hmu] at this
  have hVk : 0 < E.V - E.k := by linarith
  have hV0 : 0 < E.V := by linarith
  set h : ℝ → ℝ := fun r => (E.V - E.k) * E.mu * ((1 - r) * (E.V - r * E.k)) - E.c * E.V with hh
  have hg : ∀ r, gcubic E r = (1 - r) * h r := by
    intro r; simp only [gcubic, hh]; ring
  have hanti : ∀ x y, 0 ≤ x → x < y → y ≤ 1 → h y < h x := by
    intro x y hx hxy hy
    simp only [hh]
    have h1 : (1 - y) * (E.V - y * E.k) < (1 - x) * (E.V - x * E.k) := by
      have : (1 - x) * (E.V - x * E.k) - (1 - y) * (E.V - y * E.k)
          = (y - x) * ((E.V - E.k) + E.k * (2 - x - y)) := by ring
      have hp : 0 < (y - x) * ((E.V - E.k) + E.k * (2 - x - y)) := by
        apply mul_pos (by linarith)
        have : 0 ≤ E.k * (2 - x - y) := mul_nonneg hkpos.le (by linarith)
        linarith
      linarith
    have := mul_lt_mul_of_pos_left h1 (mul_pos hVk hmu)
    linarith
  have h0 : 0 < h 0 := by simp only [hh]; nlinarith
  have h1 : h 1 < 0 := by simp only [hh]; nlinarith
  have hcont : ContinuousOn h (Set.Icc 0 1) := by
    simp only [hh]; fun_prop
  obtain ⟨rs, ⟨hrs0, hrs1⟩, hrs⟩ :=
    intermediate_value_Icc' (show (0 : ℝ) ≤ 1 by norm_num) hcont ⟨h1.le, h0.le⟩
  have hrs0' : 0 < rs := by
    rcases hrs0.lt_or_eq with h' | h'
    · exact h'
    · subst h'; linarith
  have hrs1' : rs < 1 := by
    rcases hrs1.lt_or_eq with h' | h'
    · exact h'
    · subst h'; linarith
  refine ⟨rs, ⟨hrs0', hrs1'⟩, by rw [hg, hrs, mul_zero], ?_, ?_, ?_⟩
  · rintro r ⟨hr0, hr1⟩ hgr
    rw [hg] at hgr
    have hhr : h r = 0 := by
      rcases mul_eq_zero.mp hgr with h' | h'
      · linarith
      · exact h'
    by_contra hne
    rcases lt_or_gt_of_ne hne with hl | hl
    · have := hanti r rs hr0.le hl hrs1; linarith
    · have := hanti rs r hrs0 hl hr1.le; linarith
  · rintro r ⟨hr0, hr1⟩
    rw [hg]
    have := hanti r rs hr0.le hr1 hrs1
    apply mul_pos (by linarith) (by linarith)
  · rintro r ⟨hr0, hr1⟩
    rw [hg]
    have := hanti rs r hrs0 hr0 hr1.le
    apply mul_neg_of_pos_of_neg (by linarith) (by linarith)
