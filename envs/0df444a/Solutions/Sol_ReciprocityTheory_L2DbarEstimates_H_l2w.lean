-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.H.l2w
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:07:01.674057+00:00
-- url     : https://prove2.me/submissions/b5cbf447-1b58-4058-86f5-89d790d81126

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_SkodaWeightStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_WeightedIntegralEqLintegral
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_ae_weighted_iff_ae
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_eLpNorm_two_weighted_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.H
open MeasureTheory ReciprocityTheory.L2DbarEstimates
open scoped ENNReal InnerProductSpace
namespace ReciprocityTheory.L2DbarEstimates.H
theorem _root_.solution (n : ℕ) (M : Type*) [MeasurableSpace M] : WeightedL2Properties n M := by
  intro z ψ hψ
  refine ⟨fun P => ae_weighted_iff_ae n z hψ P, fun F => ?_, fun f hf hfin => ?_⟩
  · have hlt := Lp.eLpNorm_lt_top F
    have hw : wint n z F ψ = eLpNorm F 2 (wvol n z ψ) ^ (2 : ℝ) := by
      rw [eLpNorm_two_weighted_eq n z hψ, ← ENNReal.rpow_mul]
      norm_num
    refine ⟨?_, ?_⟩
    · rw [hw]
      exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hlt.ne
    · rw [hw, Lp.norm_def, ← ENNReal.toReal_rpow, Real.rpow_two]
  · have hmem : MemLp f 2 (wvol n z ψ) := by
      refine ⟨hf.mono_ac (withDensity_absolutelyContinuous _ _), ?_⟩
      rw [eLpNorm_two_weighted_eq n z hψ f]
      exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hfin.ne
    exact ⟨hmem.toLp f, (ae_weighted_iff_ae n z hψ (fun x => (hmem.toLp f : M → ℂ) x = f x)).mp
      (MemLp.coeFn_toLp hmem)⟩
end ReciprocityTheory.L2DbarEstimates.H
