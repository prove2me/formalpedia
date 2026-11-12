-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12Concatenation.bh12OneLevelProtocolFamily_successfulOutputCost_le_four_thirds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T05:34:16.529288+00:00
-- url     : https://prove2.me/submissions/3e7a8d07-a9ee-45ea-af60-809f122679cc

import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_QEC_Distillation_Triorthogonal_Protocol
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_Core_Overhead
import Definitions.Def_QEC_Distillation_Triorthogonal_Concatenation
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12OneLevelProtocolFamily_successfulOutputCost

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
    (q : Nat) (p : ErrorParameter) (hhalf : p.rate ≤ 1 / 2) (port : OddRow q)
    (hsmall : (bh12InputCount q : ℝ) * p.rate ≤ 1 / 4) :
    (bh12OneLevelProtocolFamily q p hhalf).successfulOutputCost port ≤
      ((4 : ℝ) / 3) * ((bh12InputCount q : ℝ) / bh12OutputCount q) := by
  have hsuccess : (3 : ℝ) / 4 ≤ rawSuccessMass q p := by
    rw [← bh12ActualRun_successProbability]
    exact bh12ActualRun_three_quarters_le_successProbability q p hsmall
  have hratioNonneg : 0 ≤ (bh12InputCount q : ℝ) / bh12OutputCount q := by
    positivity
  have hdiv :
      (bh12InputCount q : ℝ) / bh12OutputCount q / rawSuccessMass q p ≤
        ((bh12InputCount q : ℝ) / bh12OutputCount q) / ((3 : ℝ) / 4) :=
    div_le_div_of_nonneg_left hratioNonneg (by norm_num) hsuccess
  calc
    (bh12OneLevelProtocolFamily q p hhalf).successfulOutputCost port =
        (bh12InputCount q : ℝ) /
          ((bh12OutputCount q : ℝ) * rawSuccessMass q p) :=
      bh12OneLevelProtocolFamily_successfulOutputCost q p hhalf port
    _ = (bh12InputCount q : ℝ) / bh12OutputCount q / rawSuccessMass q p := by
      rw [div_div]
    _ ≤ ((bh12InputCount q : ℝ) / bh12OutputCount q) / ((3 : ℝ) / 4) := hdiv
    _ = ((4 : ℝ) / 3) * ((bh12InputCount q : ℝ) / bh12OutputCount q) := by
      ring
end QEC.Distillation.Triorthogonal.BH12Concatenation
