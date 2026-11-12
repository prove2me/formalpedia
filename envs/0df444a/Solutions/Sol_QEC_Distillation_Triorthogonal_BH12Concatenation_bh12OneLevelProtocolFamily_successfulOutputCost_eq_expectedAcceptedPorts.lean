-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12Concatenation.bh12OneLevelProtocolFamily_successfulOutputCost_eq_expectedAcceptedPorts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T05:34:00.601203+00:00
-- url     : https://prove2.me/submissions/504b7bca-96c5-4108-b32d-21a770972894

import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_QEC_Distillation_Triorthogonal_Protocol
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_Core_Overhead
import Definitions.Def_QEC_Distillation_Triorthogonal_Concatenation
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12PhysicalExpectedAcceptedPorts
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
    (q : Nat) (p : ErrorParameter) (hhalf : p.rate ≤ 1 / 2) (port : OddRow q) :
    (bh12OneLevelProtocolFamily q p hhalf).successfulOutputCost port =
      (bh12InputCount q : ℝ) /
        DependentBatch.expectedAcceptedPorts (bh12PhysicalFlaggedBatch q p) := by
  rw [bh12OneLevelProtocolFamily_successfulOutputCost,
    bh12PhysicalExpectedAcceptedPorts]
end QEC.Distillation.Triorthogonal.BH12Concatenation
