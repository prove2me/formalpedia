-- Prove2me | solution 1 for RobbinsSeqDesign.StayOrSwitch.loss_max
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T01:30:11.646152+00:00
-- url     : https://prove2.me/submissions/c000c3ee-88a1-4629-84db-4507a74a0e03

import Mathlib
import Definitions.Def_RobbinsSeqDesign_StayOrSwitch_Coins
open RobbinsSeqDesign.StayOrSwitch
private theorem loss_bound (g d : ℝ) (hd : 0 ≤ d) (hg : g < 1)
    (hdg : d ≤ g) (hs : g + d ≤ 1) :
    0 ≤ d * (1 - d / (1-g)) ∧ d * (1 - d / (1-g)) ≤ 3 - 2 * Real.sqrt 2 := by
  have ht : 0 < 1-g := by linarith
  have hr : 0 < 1-d := by linarith
  have hdt : d ≤ 1-g := by linarith
  have hsq := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hs0 := Real.sqrt_nonneg 2
  constructor
  · apply mul_nonneg hd
    have := (div_le_one ht).mpr hdt
    linarith
  · have hcomp : d^2 / (1-d) ≤ d^2 / (1-g) :=
      div_le_div_of_nonneg_left (sq_nonneg d) ht (by linarith)
    have hb : d - d^2 / (1-d) ≤ 3 - 2 * Real.sqrt 2 := by
      have hp : (d - (3 - 2 * Real.sqrt 2)) * (1-d) ≤ d^2 := by
        nlinarith [sq_nonneg (Real.sqrt 2 * d + 1 - Real.sqrt 2)]
      have hh := (le_div_iff₀ hr).mpr hp
      linarith
    have he : d * (1-d/(1-g)) = d - d^2/(1-g) := by ring
    rw [he]
    linarith

/-- Section 2, Eqs. (7)–(8) and the maximum `M₁`, p. 531: for `0 ≤ α, β ≤ 1` not both `0` and
not both `1`, `max(α, β) = γ + δ` and `0 ≤ δ[1 − δ/(1 − γ)] ≤ 3 − 2^{3/2}`; the value
`3 − 2^{3/2}` is taken at `α = 0, β = 2 − 2^{1/2}` and at `α = 2 − 2^{1/2}, β = 0`. -/
theorem solution :
    (∀ α β : ℝ, 0 ≤ α → α ≤ 1 → 0 ≤ β → β ≤ 1 → ¬(α = 0 ∧ β = 0) → ¬(α = 1 ∧ β = 1) →
        max α β = gamma α β + delta α β ∧
          0 ≤ delta α β * (1 - delta α β / (1 - gamma α β)) ∧
          delta α β * (1 - delta α β / (1 - gamma α β)) ≤ 3 - 2 * Real.sqrt 2) ∧
      delta 0 (2 - Real.sqrt 2) * (1 - delta 0 (2 - Real.sqrt 2) / (1 - gamma 0 (2 - Real.sqrt 2)))
        = 3 - 2 * Real.sqrt 2 ∧
      delta (2 - Real.sqrt 2) 0 * (1 - delta (2 - Real.sqrt 2) 0 / (1 - gamma (2 - Real.sqrt 2) 0))
        = 3 - 2 * Real.sqrt 2 := by
  have hs0 := Real.sqrt_nonneg 2
  have hs2 := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hslt : Real.sqrt 2 < 2 := by nlinarith
  have hsn : Real.sqrt 2 ≠ 0 := by nlinarith
  refine ⟨?_, ?_, ?_⟩
  · intro α β ha0 ha1 hb0 hb1 hab0 hab1
    have hg : gamma α β < 1 := by
      unfold gamma
      by_contra h
      have : α = 1 ∧ β = 1 := by constructor <;> linarith
      exact hab1 this
    have hd : 0 ≤ delta α β := by unfold delta; positivity
    have hdg : delta α β ≤ gamma α β := by
      unfold delta gamma
      rw [div_le_div_iff_of_pos_right (by norm_num : (0:ℝ) < 2)]
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have he : max α β = gamma α β + delta α β := by
      unfold gamma delta
      rcases le_total α β with h | h
      · rw [max_eq_right h, abs_of_nonpos (by linarith)]; ring
      · rw [max_eq_left h, abs_of_nonneg (by linarith)]; ring
    refine ⟨he, loss_bound _ _ hd hg hdg ?_⟩
    rw [← he]
    exact max_le ha1 hb1
  · unfold delta gamma
    rw [abs_of_nonpos (by linarith)]
    field_simp
    nlinarith
  · unfold delta gamma
    rw [abs_of_nonneg (by linarith)]
    field_simp
    nlinarith


#print axioms solution
