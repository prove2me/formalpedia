-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12Concatenation.bh12OneLevelProtocolFamily_successfulOutputCost
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:45:12.747363+00:00
-- url     : https://prove2.me/submissions/12eaaf6d-50b1-4915-ab68-7407db01381c

import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_QEC_Distillation_Triorthogonal_Protocol
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_Core_Overhead
import Definitions.Def_QEC_Distillation_Triorthogonal_Concatenation
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12OneLevelProtocolFamily_inputResourceCount
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12OneLevelProtocolFamily_outputResourceCount
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12OneLevelProtocolFamily_successProbability

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
    (p : ErrorParameter) (hhalf : p.rate ≤ 1 / 2) (port : OddRow q) :
    (bh12OneLevelProtocolFamily q p hhalf).successfulOutputCost port =
      (bh12InputCount q : ℝ) /
        ((bh12OutputCount q : ℝ) * rawSuccessMass q p) := by
  unfold DistillationProtocolFamily.successfulOutputCost
  rw [bh12OneLevelProtocolFamily_inputResourceCount,
    bh12OneLevelProtocolFamily_outputResourceCount,
    bh12OneLevelProtocolFamily_successProbability]
end QEC.Distillation.Triorthogonal.BH12Concatenation
