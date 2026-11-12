-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12Concatenation.bh12PathTypedSuccessfulOutputCost_le_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:45:33.641196+00:00
-- url     : https://prove2.me/submissions/4cb280cf-194a-4671-8ce4-83475b915544

import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_QEC_Distillation_Triorthogonal_Protocol
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_Core_Overhead
import Definitions.Def_QEC_Distillation_Triorthogonal_Concatenation
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12PathTypedSuccessfulOutputCost_eq

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Triorthogonal QEC.Distillation.Triorthogonal.BH12Concatenation
open Semantics
open BH12EvenFamily
open BH12NoisyInjection
open BH12Protocol
open Filter Topology
namespace QEC.Distillation.Triorthogonal.BH12Concatenation
theorem _root_.solution (q : Nat)
    (p : ErrorParameter)
    (hsmall : (bh12InputCount q : ℝ) * p.rate ≤ 1 / 4)
    (hhalf : p.rate ≤ 1 / 2)
    (hstrong : quadraticCoefficient q * p.rate ≤ 1 / 2)
    (z : Nat) (path : depthOutputPath q z) :
    bh12PathTypedSuccessfulOutputCost q p hsmall hhalf hstrong z path ≤
      2 * ((bh12InputCount q : ℝ) / bh12OutputCount q) ^ z := by
  rw [bh12PathTypedSuccessfulOutputCost_eq]
  have hratioNonneg : 0 ≤ ((bh12InputCount q : ℝ) / bh12OutputCount q) ^ z :=
    pow_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) _
  have hyieldHalf : (1 : ℝ) / 2 ≤ bh12PathYieldFactorProduct q p z path :=
    bh12PathYieldFactorProduct_half_le q p hsmall hhalf hstrong z path
  calc
    ((bh12InputCount q : ℝ) / bh12OutputCount q) ^ z /
        bh12PathYieldFactorProduct q p z path ≤
        ((bh12InputCount q : ℝ) / bh12OutputCount q) ^ z / ((1 : ℝ) / 2) :=
      div_le_div_of_nonneg_left hratioNonneg (by norm_num) hyieldHalf
    _ = 2 * ((bh12InputCount q : ℝ) / bh12OutputCount q) ^ z := by ring
end QEC.Distillation.Triorthogonal.BH12Concatenation
