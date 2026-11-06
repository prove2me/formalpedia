-- Prove2me | solution 1 for ProbabilityTheory.levySmallJumpPath_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T09:09:23.900198+00:00
-- url     : https://prove2.me/submissions/0d304e7c-6691-464b-974e-84790e214491

import Definitions.Def_LeanLevy_RandomMeasure_LevyJumpPath
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Complex ComplexConjugate Set Filter Topology Finset ProbabilityTheory
open scoped NNReal ENNReal
variable {Ω : Type} [MeasurableSpace Ω] {K : ℕ → Ω → ℕ}
  {X : ℕ → ℕ → Ω → ℝ × ℝ} {ν : Measure ℝ} [SigmaFinite ν]
  {μ : Measure Ω} {A : Set ℝ}

theorem solution
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν) :
    levySmallJumpPath hd hν 0 = 0 := by
  classical
  funext ω
  have hzero (B : Set ℝ) : levyBandPath K X ν B 0 ω = 0 := by
    have hband : ((Set.Ioc (0 : ℝ) 0 ×ˢ B).indicator
        fun p : ℝ × ℝ => p.2) = fun _ => 0 := by
      rw [Set.Ioc_self, Set.empty_prod, Set.indicator_empty]
    simp only [levyBandPath, zero_mul, sub_zero, bandJumpSum, hband,
      pieceSum, Finset.sum_const_zero, tsum_zero]
  have hconst : (fun j => if ω ∈ levySmallJumpGoodSet hd hν
      then levyBandPath K X ν (levyAnnulus (levyTruncationSeq hν j))
        (max (0 : ℝ) 0) ω else 0) = fun _ => (0 : ℝ) := by
    funext j
    simp only [max_self]
    split
    · exact hzero (levyAnnulus (levyTruncationSeq hν j))
    · rfl
  simp only [levySmallJumpPath, Pi.zero_apply]
  rw [hconst]
  exact tendsto_const_nhds.limUnder_eq
