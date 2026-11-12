-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12Concatenation.bh12PathTypedSuccessfulOutputCost_le_two_rpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:48:31.606828+00:00
-- url     : https://prove2.me/submissions/97748c2f-1a5f-47bf-8fb2-c4a9225db770

import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_QEC_Distillation_Triorthogonal_Protocol
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_Core_Overhead
import Definitions.Def_QEC_Distillation_Triorthogonal_Concatenation
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12BlockRatio_rpow_two_pow_eq_pow
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12PathTypedSuccessfulOutputCost_le_two

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
    (hq : 0 < q) (z : Nat) (path : depthOutputPath q z) :
    bh12PathTypedSuccessfulOutputCost q p hsmall hhalf hstrong z path ≤
      2 * Real.rpow ((2 : ℝ) ^ z) (bh12BlockExponent q) := by
  rw [bh12BlockRatio_rpow_two_pow_eq_pow hq z]
  exact bh12PathTypedSuccessfulOutputCost_le_two q p hsmall hhalf hstrong z path
end QEC.Distillation.Triorthogonal.BH12Concatenation
