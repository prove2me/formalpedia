-- Prove2me | solution 1 for QualityEncroach.Differ.reduced_profit_high
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T14:47:24.760718+00:00
-- url     : https://prove2.me/submissions/1aef449a-762d-4797-8846-ae40bfa08ddd

import Mathlib
import Definitions.Def_QualityEncroach_Differ_Game
import Definitions.Def_QualityEncroach_Differ_Reduced

open QualityEncroach.Differ in
theorem solution (k c : ℝ) (hk : 0 < k) (hc : 0 ≤ c) (t u : ℝ) (hu : 0 < u)
    (ht0 : 0 < t) (ht1 : t ≤ 1) :
    mfrPayoff k c ⟨wH k c t u, u, t, qR7 k c (wH k c t u) u t, qM7 k c (wH k c t u) u t⟩ =
        PiH k c t u ∧
    ∀ w : ℝ, w ≠ wH k c t u →
      mfrPayoff k c ⟨w, u, t, qR7 k c w u t, qM7 k c w u t⟩ < PiH k c t u := by
  have h2t : (2 - t) ≠ 0 := by intro h; linarith
  have h85 : (8 - 5 * t) ≠ 0 := by intro h; linarith
  have h85' : (8 - t * 5) ≠ 0 := by intro h; linarith
  have h2t' : (t - 2) ≠ 0 := by intro h; linarith
  have hu0 : u ≠ 0 := hu.ne'
  have ht0' : t ≠ 0 := ht0.ne'
  have key : ∀ w : ℝ, mfrPayoff k c ⟨w, u, t, qR7 k c w u t, qM7 k c w u t⟩ =
      PiH k c t u - (8 - 5 * t) / (4 * t * u * (2 - t) ^ 2) * (w - wH k c t u) ^ 2 := by
    intro w
    unfold mfrPayoff priceM qR7 qM7 PiH wH
    simp only [if_pos ht1]
    field_simp <;> ring_nf <;> field_simp <;> ring_nf
  refine ⟨?_, fun w hw => ?_⟩
  · rw [key]; simp
  · rw [key]
    have hpos : 0 < (8 - 5 * t) / (4 * t * u * (2 - t) ^ 2) := by
      apply div_pos
      · linarith
      · have : 0 < (2 - t) ^ 2 := by positivity
        positivity
    have hsq : 0 < (w - wH k c t u) ^ 2 := by
      have : w - wH k c t u ≠ 0 := sub_ne_zero.mpr hw
      positivity
    nlinarith [mul_pos hpos hsq]
