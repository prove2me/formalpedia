-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12Concatenation.bh12PathTypedSuccessfulOutputCost_le_quadraticEnvelope_polylog
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:51:41.440359+00:00
-- url     : https://prove2.me/submissions/1b7fbd7e-6b93-43fa-a3d9-5c7d1fa8f85c

import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_QEC_Distillation_Triorthogonal_Protocol
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_Core_Overhead
import Definitions.Def_QEC_Distillation_Triorthogonal_Concatenation
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12BlockExponent_pos
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12QuadraticEnvelopeLogGrowthBase_pos
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12TwoPow_mul_quadraticEnvelopeLogGrowthBase_le_log
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12PathTypedSuccessfulOutputCost_le_two_rpow

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Triorthogonal QEC.Distillation.Triorthogonal.BH12Concatenation
open Semantics
open BH12EvenFamily
open BH12NoisyInjection
open BH12Protocol
open Filter Topology
namespace QEC.Distillation.Triorthogonal.BH12Concatenation
theorem _root_.solution
    (q : Nat) (p : ErrorParameter)
    (hsmall : (bh12InputCount q : ℝ) * p.rate ≤ 1 / 4)
    (hhalf : p.rate ≤ 1 / 2)
    (hstrong : quadraticCoefficient q * p.rate ≤ 1 / 2)
    (hp : 0 < p.rate) (hq : 0 < q) (z : Nat) (path : depthOutputPath q z) :
    bh12PathTypedSuccessfulOutputCost q p hsmall hhalf hstrong z path ≤
      bh12QuadraticEnvelopeCostCoefficient q p *
        Real.rpow (Real.log (1 / bh12QuadraticEnvelope q p z))
          (bh12BlockExponent q) := by
  have hbasePos : 0 < bh12QuadraticEnvelopeLogGrowthBase q p :=
    bh12QuadraticEnvelopeLogGrowthBase_pos q p hp hstrong
  have hexponentPos : 0 < bh12BlockExponent q := bh12BlockExponent_pos hq
  have hlog :
      (2 : ℝ) ^ z * bh12QuadraticEnvelopeLogGrowthBase q p ≤
        Real.log (1 / bh12QuadraticEnvelope q p z) :=
    bh12TwoPow_mul_quadraticEnvelopeLogGrowthBase_le_log q p hp hhalf hstrong z
  have hpowComparison :
      Real.rpow ((2 : ℝ) ^ z * bh12QuadraticEnvelopeLogGrowthBase q p)
          (bh12BlockExponent q) ≤
        Real.rpow (Real.log (1 / bh12QuadraticEnvelope q p z))
          (bh12BlockExponent q) :=
    Real.rpow_le_rpow
      (mul_nonneg (by positivity) hbasePos.le) hlog hexponentPos.le
  have hfactorization :
      Real.rpow ((2 : ℝ) ^ z * bh12QuadraticEnvelopeLogGrowthBase q p)
          (bh12BlockExponent q) =
        Real.rpow ((2 : ℝ) ^ z) (bh12BlockExponent q) *
          Real.rpow (bh12QuadraticEnvelopeLogGrowthBase q p)
            (bh12BlockExponent q) :=
    Real.mul_rpow (by positivity) hbasePos.le
  have hbaseRpowPos :
      0 < Real.rpow (bh12QuadraticEnvelopeLogGrowthBase q p)
        (bh12BlockExponent q) :=
    Real.rpow_pos_of_pos hbasePos _
  rw [hfactorization] at hpowComparison
  have htwiceComparison :
      2 * Real.rpow ((2 : ℝ) ^ z) (bh12BlockExponent q) *
          Real.rpow (bh12QuadraticEnvelopeLogGrowthBase q p)
            (bh12BlockExponent q) ≤
        2 * Real.rpow (Real.log (1 / bh12QuadraticEnvelope q p z))
          (bh12BlockExponent q) := by
    calc
      2 * Real.rpow ((2 : ℝ) ^ z) (bh12BlockExponent q) *
          Real.rpow (bh12QuadraticEnvelopeLogGrowthBase q p)
            (bh12BlockExponent q) =
          2 * (Real.rpow ((2 : ℝ) ^ z) (bh12BlockExponent q) *
            Real.rpow (bh12QuadraticEnvelopeLogGrowthBase q p)
              (bh12BlockExponent q)) := by ring
      _ ≤ 2 * Real.rpow (Real.log (1 / bh12QuadraticEnvelope q p z))
          (bh12BlockExponent q) :=
        mul_le_mul_of_nonneg_left hpowComparison (by norm_num)
  calc
    bh12PathTypedSuccessfulOutputCost q p hsmall hhalf hstrong z path ≤
        2 * Real.rpow ((2 : ℝ) ^ z) (bh12BlockExponent q) :=
      bh12PathTypedSuccessfulOutputCost_le_two_rpow q p hsmall hhalf hstrong hq z path
    _ =
        (2 * Real.rpow ((2 : ℝ) ^ z) (bh12BlockExponent q) *
          Real.rpow (bh12QuadraticEnvelopeLogGrowthBase q p)
            (bh12BlockExponent q)) /
          Real.rpow (bh12QuadraticEnvelopeLogGrowthBase q p)
            (bh12BlockExponent q) := by
      field_simp [ne_of_gt hbaseRpowPos]
    _ ≤
        (2 * Real.rpow (Real.log (1 / bh12QuadraticEnvelope q p z))
          (bh12BlockExponent q)) /
          Real.rpow (bh12QuadraticEnvelopeLogGrowthBase q p)
            (bh12BlockExponent q) :=
      div_le_div_of_nonneg_right
        htwiceComparison hbaseRpowPos.le
    _ =
        bh12QuadraticEnvelopeCostCoefficient q p *
          Real.rpow (Real.log (1 / bh12QuadraticEnvelope q p z))
            (bh12BlockExponent q) := by
      unfold bh12QuadraticEnvelopeCostCoefficient
      field_simp [ne_of_gt hbaseRpowPos]
end QEC.Distillation.Triorthogonal.BH12Concatenation
