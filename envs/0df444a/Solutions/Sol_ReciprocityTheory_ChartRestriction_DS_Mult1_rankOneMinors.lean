-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Mult1.rankOneMinors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:12:44.842638+00:00
-- url     : https://prove2.me/submissions/ed344618-873d-4c79-8903-46edd7a79456

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_MultiplicityOne_TransposeUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_MultiplicityOne_JRankOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Mult1
namespace ReciprocityTheory.ChartRestriction.DS.Mult1
theorem _root_.solution : RankOneMinors := by
  intro X κ hherm hpos hmin
  by_cases h : ∃ x0, κ x0 x0 ≠ 0
  · obtain ⟨x0, hx0⟩ := h
    have him : (κ x0 x0).im = 0 := by
      have h1 := congrArg Complex.im (hherm x0 x0)
      simp [Complex.star_def] at h1
      linarith
    have hk0 : κ x0 x0 = (((κ x0 x0).re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
    have hr : 0 < (κ x0 x0).re := by
      rcases (hpos x0).lt_or_eq with h | h
      · exact h
      · exact (hx0 (by rw [hk0, ← h]; simp)).elim
    generalize (κ x0 x0).re = r at hk0 hr
    refine ⟨fun x => κ x x0 / (Real.sqrt r : ℂ), fun x y => ?_⟩
    show κ x y = κ x x0 / (Real.sqrt r : ℂ) * star (κ y x0 / (Real.sqrt r : ℂ))
    have hs : (Real.sqrt r : ℂ) * (Real.sqrt r : ℂ) = (r : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hr.le]
    have hst : star (κ y x0 / (Real.sqrt r : ℂ)) = κ x0 y / (Real.sqrt r : ℂ) := by
      rw [star_div₀, ← hherm x0 y]
      congr 1
      exact Complex.conj_ofReal _
    rw [hst, div_mul_div_comm, hs, ← hk0, hmin x x0 x0 y, mul_div_assoc, div_self hx0, mul_one]
  · push_neg at h
    refine ⟨fun _ => 0, fun x y => ?_⟩
    simp only [zero_mul]
    have h1 := hmin x y y x
    rw [h x, zero_mul, hherm y x] at h1
    have e : κ x y * star (κ x y) = (Complex.normSq (κ x y) : ℂ) := Complex.mul_conj _
    rw [e] at h1
    exact Complex.normSq_eq_zero.mp (by exact_mod_cast h1)
end ReciprocityTheory.ChartRestriction.DS.Mult1
