-- Prove2me | solution 1 for ProbabilityTheory.ae_isCadlag_levyJumpPath
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T22:50:49.205964+00:00
-- url     : https://prove2.me/submissions/d0b1aae7-704b-459a-bc62-6a966bdae00c

import Definitions.Def_LeanLevy_RandomMeasure_LevyJumpPath
import Theorems.Thm_ProbabilityTheory_ae_isCadlag_levyLargeJumpSum
import Theorems.Thm_Continuous_isCadlag
import Theorems.Thm_ProbabilityTheory_IsCadlag_add
import Theorems.Thm_ProbabilityTheory_isCadlag_levySmallJumpPath
import Theorems.Thm_isCadlag_comp_nnrealCoe
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory Filter Set Topology Complex
open scoped NNReal ENNReal BigOperators
variable {Ω : Type} [MeasurableSpace Ω] {K : ℕ → Ω → ℕ}
  {X : ℕ → ℕ → Ω → ℝ × ℝ} {ν : Measure ℝ} [SigmaFinite ν] {μ : Measure Ω}

theorem solution [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν) (b : ℝ) :
    ∀ᵐ ω ∂μ, IsCadlag (fun t : ℝ≥0 => levyJumpPath hd hν b t ω) := by
  filter_upwards [ae_isCadlag_levyLargeJumpSum hd hν] with ω hω
  have hdrift : IsCadlag (fun s : ℝ => b * s) :=
    (by fun_prop : Continuous fun s : ℝ => b * s).isCadlag
  have hcadReal : IsCadlag (fun s : ℝ =>
      b * s + levyLargeJumpSum K X s ω + levySmallJumpPath hd hν s ω) :=
    (hdrift.add hω).add (isCadlag_levySmallJumpPath hd hν ω)
  simpa only [levyJumpPath] using isCadlag_comp_nnrealCoe hcadReal