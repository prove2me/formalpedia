-- Prove2me | solution 1 for avram_chat24_right_path_measurable_core
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:08:29.049547+00:00
-- url     : https://prove2.me/submissions/777ed947-f90d-42c8-9a34-c8847e3a5a91

import Mathlib
import Theorems.Thm_avram_chat24_right_grid_limit_core
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology

theorem solution (f : ℝ≥0 → ℝ)
    (hf : ∀ t, ContinuousWithinAt f (Ici t) t) : Measurable f := by
  let u (n : ℕ) (t : ℝ≥0) : ℝ≥0 :=
    ((⌊((n + 1 : ℕ) : ℝ) * (t : ℝ)⌋₊ + 1 : ℕ) : ℝ≥0) /
      ((n + 1 : ℕ) : ℝ≥0)
  have hm (n : ℕ) : Measurable (fun t => f (u n t)) := by
    exact (measurable_of_countable (fun j : ℕ =>
      f (((j + 1 : ℕ) : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0)))).comp
      ((continuous_subtype_val.measurable.const_mul ((n + 1 : ℕ) : ℝ)).nat_floor)
  have hl (t : ℝ≥0) : Tendsto (fun n => f (u n t)) atTop (nhds (f t)) :=
    (hf t).tendsto.comp (avram_chat24_right_grid_limit_core t)
  exact measurable_of_tendsto_metrizable hm (tendsto_pi_nhds.2 hl)
