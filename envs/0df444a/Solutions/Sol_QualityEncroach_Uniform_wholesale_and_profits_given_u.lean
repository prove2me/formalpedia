-- Prove2me | solution 1 for QualityEncroach.Uniform.wholesale_and_profits_given_u
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:02:47.666924+00:00
-- url     : https://prove2.me/submissions/b7d3b5d7-aeec-4586-9e3b-95659b4f0ab7

import Mathlib
import Definitions.Def_QualityEncroach_Uniform_Game

set_option autoImplicit false
open QualityEncroach.Uniform

theorem solution (k c : ℝ) (hk : 0 < k) (hc : 0 ≤ c) (u : ℝ) (hu : 0 < u) :
    (∀ w : ℝ, w ≠ wU k c u →
        mfrPayoff k c ⟨w, u, qUR k c w u, qUM k c w u⟩ <
          mfrPayoff k c ⟨wU k c u, u, qUR k c (wU k c u) u, qUM k c (wU k c u) u⟩) ∧
    qUR k c (wU k c u) u = 2 * c / (3 * u) ∧
    qUM k c (wU k c u) u = -(k * u) / 2 - 5 * c / (6 * u) + 1 / 2 ∧
    mfrPayoff k c ⟨wU k c u, u, qUR k c (wU k c u) u, qUM k c (wU k c u) u⟩ = PiUM k c u ∧
    retailerPayoff ⟨wU k c u, u, qUR k c (wU k c u) u, qUM k c (wU k c u) u⟩ = PiUR c u := by
  have hu' := hu.ne'
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro w hne
    have hne' : 0 < (w - wU k c u) ^ 2 := by
      have : w - wU k c u ≠ 0 := sub_ne_zero.2 hne
      positivity
    have key : mfrPayoff k c ⟨wU k c u, u, qUR k c (wU k c u) u, qUM k c (wU k c u) u⟩
        - mfrPayoff k c ⟨w, u, qUR k c w u, qUM k c w u⟩
        = 3 / (4 * u) * (w - wU k c u) ^ 2 := by
      simp only [mfrPayoff, qUR, qUM, wU]
      field_simp
      ring
    have : 0 < 3 / (4 * u) * (w - wU k c u) ^ 2 := by positivity
    linarith
  · unfold qUR wU; field_simp; ring
  · unfold qUM wU; field_simp; ring
  · simp only [mfrPayoff, qUR, qUM, wU, PiUM]; field_simp; ring
  · simp only [retailerPayoff, qUR, qUM, wU, PiUR]; field_simp; ring
