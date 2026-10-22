-- Prove2me | solution 1 for TsayQF.EffQF.qf_purchase
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:33:33.037349+00:00
-- url     : https://prove2.me/submissions/23468449-80b9-4f1d-832e-736f3904bc76

import Mathlib
import Definitions.Def_TsayQF_EffQF_Model
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open TsayQF.EffQF

theorem solution (D : Data) (c : ℝ) (hcu : D.u < c) (hcp : c < D.p + D.s) :
    ∀ μ a b r, a ≤ b → r ∈ Set.Icc a b →
      (IsMaxOn (fun r' => G D c r' μ) (Set.Icc a b) r ↔ r = clip μ a b) := by
  intro μ a b r hab hr
  have hG1 : ∀ x : ℝ, x ≤ μ → G D c x μ = (D.p + D.s - c) * x - D.s * μ := by
    intro x hx
    unfold G
    rw [min_eq_right hx, max_eq_left (by linarith : (0:ℝ) ≤ μ - x),
      max_eq_right (by linarith : x - μ ≤ 0)]
    ring
  have hG2 : ∀ x : ℝ, μ ≤ x → G D c x μ = (D.u - c) * x + (D.p - D.u) * μ := by
    intro x hx
    unfold G
    rw [min_eq_left hx, max_eq_right (by linarith : μ - x ≤ 0),
      max_eq_left (by linarith : (0:ℝ) ≤ x - μ)]
    ring
  have hclipmem : clip μ a b ∈ Set.Icc a b :=
    ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩
  have key : ∀ r' ∈ Set.Icc a b, r' ≠ clip μ a b → G D c r' μ < G D c (clip μ a b) μ := by
    intro r' hr' hne
    unfold clip at hne ⊢
    rcases le_or_gt μ a with h1 | h1
    · have hc : max a (min μ b) = a := max_eq_left ((min_le_left _ _).trans h1)
      rw [hc] at hne ⊢
      have : a < r' := lt_of_le_of_ne hr'.1 (Ne.symm hne)
      rw [hG2 r' (by linarith), hG2 a h1]
      nlinarith
    · rcases le_or_gt b μ with h2 | h2
      · have hc : max a (min μ b) = b := by
          rw [min_eq_right h2]; exact max_eq_right hab
        rw [hc] at hne ⊢
        have : r' < b := lt_of_le_of_ne hr'.2 hne
        rw [hG1 r' (by linarith), hG1 b h2]
        nlinarith
      · have hc : max a (min μ b) = μ := by
          rw [min_eq_left h2.le]; exact max_eq_right h1.le
        rw [hc] at hne ⊢
        rcases lt_or_gt_of_ne hne with h3 | h3
        · rw [hG1 r' h3.le, hG1 μ le_rfl]
          nlinarith
        · rw [hG2 r' h3.le, hG1 μ le_rfl]
          nlinarith
  constructor
  · intro h
    by_contra hne
    have h1 := key r hr hne
    have h2 : G D c (clip μ a b) μ ≤ G D c r μ := isMaxOn_iff.mp h _ hclipmem
    linarith
  · intro h
    subst h
    rw [isMaxOn_iff]
    intro x hx
    by_cases hx' : x = clip μ a b
    · exact le_of_eq (by rw [hx'])
    · exact (key x hx hx').le
