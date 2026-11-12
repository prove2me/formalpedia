-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12Concatenation.bh12PhysicalPooledExpectedAcceptedPorts_pos_of_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T05:33:26.604496+00:00
-- url     : https://prove2.me/submissions/585c0718-6732-4ea0-b5d1-476d7af7f64d

import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_QEC_Distillation_Triorthogonal_Protocol
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_Core_Overhead
import Definitions.Def_QEC_Distillation_Triorthogonal_Concatenation
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12PhysicalPooledExpectedAcceptedPorts

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
    (q : Nat) (p : ErrorParameter) (count : Nat)
    (hsmall : (bh12InputCount q : ℝ) * p.rate ≤ 1 / 4)
    (hcount : count ≠ 0) (hports : 0 < bh12OutputCount q) :
    0 < DependentBatch.pooledExpectedAcceptedPorts count
      (bh12PhysicalFlaggedPool q p count) := by
  rw [bh12PhysicalPooledExpectedAcceptedPorts]
  have hsuccess : 0 < rawSuccessMass q p := by
    rw [← bh12ActualRun_successProbability]
    exact lt_of_lt_of_le (by norm_num)
      (bh12ActualRun_three_quarters_le_successProbability q p hsmall)
  have hcountReal : 0 < (count : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hcount
  have hportsReal : 0 < (bh12OutputCount q : ℝ) := by
    exact_mod_cast hports
  exact mul_pos (mul_pos hcountReal hportsReal) hsuccess
end QEC.Distillation.Triorthogonal.BH12Concatenation
