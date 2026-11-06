-- Prove2me | solution 1 for ProbabilityTheory.charFun_map_levyJumpPath
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T04:24:27.770472+00:00
-- url     : https://prove2.me/submissions/35173e8d-7698-4666-9f73-a19f1c68045b

import Definitions.Def_LeanLevy_RandomMeasure_LevyJumpPath
import Theorems.Thm_ProbabilityTheory_levyJumpPath_ae_eq
import Theorems.Thm_ProbabilityTheory_charFun_map_levyJumpProcess
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory Filter Set Topology Complex
open scoped NNReal ENNReal BigOperators
variable {Ω : Type} [MeasurableSpace Ω] {K : ℕ → Ω → ℕ}
  {X : ℕ → ℕ → Ω → ℝ × ℝ} {ν : Measure ℝ} [SigmaFinite ν] {μ : Measure Ω}

theorem solution [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    (b : ℝ) (t : ℝ≥0) (ξ : ℝ) :
    charFun (μ.map (levyJumpPath hd hν b t)) ξ
      = Complex.exp (((t : ℝ) : ℂ) * (LevyKhintchineTriple.mk b 0 ν hν).exponent ξ) := by
  rw [Measure.map_congr (levyJumpPath_ae_eq hd hν b t), charFun_map_levyJumpProcess hd hν b t ξ]
