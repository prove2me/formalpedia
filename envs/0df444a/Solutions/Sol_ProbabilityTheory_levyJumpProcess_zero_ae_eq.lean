-- Prove2me | solution 1 for ProbabilityTheory.levyJumpProcess_zero_ae_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T04:28:00.259054+00:00
-- url     : https://prove2.me/submissions/8a249da0-c513-4c57-beac-b2d7259a1a7f

import Definitions.Def_LeanLevy_RandomMeasure_LevyJumpLaw
import Theorems.Thm_ProbabilityTheory_charFun_map_levyJumpProcess_sub
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
variable {Ω : Type} [MeasurableSpace Ω] {K : ℕ → Ω → ℕ}
  {X : ℕ → ℕ → Ω → ℝ × ℝ} {ν : Measure ℝ} [SigmaFinite ν]
  {μ : Measure Ω}
theorem solution [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ)
    (hν : IsLevyMeasure ν) (b : ℝ) :
    levyJumpProcess hd hν b 0 =ᵐ[μ] fun _ => 0 := by
  have hz : levyCompensatedSmallJump hd hν 0 = 0 := by
    rw [← norm_eq_zero, Lp.norm_def, levyCompensatedSmallJump,
      eLpNorm_compensatedPoissonIntegral, eLpNorm_congr_ae (MemLp.coeFn_toLp _),
      Set.Ioc_self, Set.empty_prod, Set.indicator_empty]
    simp
  have h0 : (fun ω => levyCompensatedSmallJump hd hν 0 ω) =ᵐ[μ] fun _ => 0 := by
    rw [hz]
    exact Lp.coeFn_zero ℝ 2 μ
  have hLarge (ω : Ω) : levyLargeJumpSum K X 0 ω = 0 := by
    have hband : ((Set.Ioc (0 : ℝ) 0 ×ˢ {x : ℝ | 1 ≤ |x|}).indicator fun p : ℝ × ℝ => p.2)
        = fun _ => 0 := by
      rw [Set.Ioc_self, Set.empty_prod, Set.indicator_empty]
    simp only [levyLargeJumpSum, hband, pieceSum, Finset.sum_const_zero, tsum_zero]
  filter_upwards [h0] with ω hω
  simp only [levyJumpProcess, NNReal.coe_zero, mul_zero, hLarge ω, zero_add]
  exact hω
