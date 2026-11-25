-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Laplace.mono_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:12:44.6889+00:00
-- url     : https://prove2.me/submissions/47f1bf2b-8687-4fd1-b2a9-f2a9830d023f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_Laplace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex Filter Topology Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.Laplace
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]
namespace ReciprocityTheory.ChartRestriction.DS.Lap.Laplace
theorem _root_.solution {x s t : ℝ} (hx : 0 ≤ x) (hs : 0 < s) (hst : s ≤ t) :
    (1 + x / s) ^ s ≤ (1 + x / t) ^ t := by
  have ht : 0 < t := lt_of_lt_of_le hs hst
  have hs' : s ≠ 0 := hs.ne'
  have ht' : t ≠ 0 := ht.ne'
  have hp0 : 0 ≤ s / t := div_nonneg hs.le ht.le
  have hp1 : s / t ≤ 1 := (div_le_one ht).2 hst
  have hb : 0 ≤ 1 + x / s := add_nonneg zero_le_one (div_nonneg hx hs.le)
  have key : (1 + x / s) ^ (s / t) ≤ 1 + x / t := by
    have h := Real.geom_mean_le_arith_mean2_weighted hp0 (sub_nonneg.2 hp1) hb zero_le_one
      (by ring : s / t + (1 - s / t) = 1)
    rw [Real.one_rpow, mul_one] at h
    calc (1 + x / s) ^ (s / t) ≤ s / t * (1 + x / s) + (1 - s / t) * 1 := h
      _ = 1 + x / t := by field_simp <;> ring
  calc (1 + x / s) ^ s = ((1 + x / s) ^ (s / t)) ^ t := by
        rw [← Real.rpow_mul hb]
        congr 1
        field_simp
    _ ≤ (1 + x / t) ^ t := Real.rpow_le_rpow (Real.rpow_nonneg hb _) key ht.le
end ReciprocityTheory.ChartRestriction.DS.Lap.Laplace
