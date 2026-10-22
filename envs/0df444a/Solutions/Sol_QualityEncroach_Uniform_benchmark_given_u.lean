-- Prove2me | solution 1 for QualityEncroach.Uniform.benchmark_given_u
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:00:01.057724+00:00
-- url     : https://prove2.me/submissions/3fdf1749-7093-409e-b682-a6986ae97737

import Mathlib
import Definitions.Def_QualityEncroach_Uniform_Game

set_option autoImplicit false
open QualityEncroach.Uniform

theorem solution (k u : ℝ) (hk : 0 < k) (hu : 0 < u) (huk : u < 1 / k) :
    (∀ w : ℝ, 0 ≤ qRN w u → ∀ qR : ℝ, 0 ≤ qR → qR ≠ qRN w u →
        benchRetailerPayoff ⟨w, u, qR⟩ < benchRetailerPayoff ⟨w, u, qRN w u⟩) ∧
    (∀ w : ℝ, w ≠ wN k u →
        (w - k * u ^ 2) * qRN w u < (wN k u - k * u ^ 2) * qRN (wN k u) u) ∧
    qRN (wN k u) u = 1 / 4 - k * u / 4 ∧
    benchMfrPayoff k ⟨wN k u, u, qRN (wN k u) u⟩ = PiNM k u ∧
    benchRetailerPayoff ⟨wN k u, u, qRN (wN k u) u⟩ = PiNR k u := by
  have hu' := hu.ne'
  have h3 : qRN (wN k u) u = 1 / 4 - k * u / 4 := by
    unfold qRN wN; field_simp; ring
  refine ⟨?_, ?_, h3, ?_, ?_⟩
  · intro w _ qR _ hne
    simp only [benchRetailerPayoff]
    set b := qRN w u with hb
    have hwb : w = u - 2 * u * b := by rw [hb]; unfold qRN; field_simp; ring
    have hne' : 0 < (qR - b) ^ 2 := by
      have : qR - b ≠ 0 := sub_ne_zero.2 hne
      positivity
    rw [hwb]
    nlinarith [mul_pos hu hne']
  · intro w hne
    have hne' : 0 < (w - wN k u) ^ 2 := by
      have : w - wN k u ≠ 0 := sub_ne_zero.2 hne
      positivity
    have : (wN k u - k * u ^ 2) * qRN (wN k u) u - (w - k * u ^ 2) * qRN w u
        = (w - wN k u) ^ 2 / (2 * u) := by
      unfold qRN wN; field_simp; ring
    have h2 : 0 < (w - wN k u) ^ 2 / (2 * u) := by positivity
    linarith
  · simp only [benchMfrPayoff, PiNM]; rw [h3]; unfold wN; ring
  · simp only [benchRetailerPayoff, PiNR]; rw [h3]; unfold wN; ring
