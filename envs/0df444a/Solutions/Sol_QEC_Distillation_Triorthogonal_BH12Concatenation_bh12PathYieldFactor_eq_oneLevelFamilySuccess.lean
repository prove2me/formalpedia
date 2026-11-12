-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12Concatenation.bh12PathYieldFactor_eq_oneLevelFamilySuccess
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T05:35:20.066655+00:00
-- url     : https://prove2.me/submissions/0e0959d9-8516-4588-b96e-20535d79a9cc

import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_QEC_Distillation_Triorthogonal_Protocol
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_Core_Overhead
import Definitions.Def_QEC_Distillation_Triorthogonal_Concatenation
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12OneLevelProtocolFamily_successProbability
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm


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
    (p : ErrorParameter) (z : Nat) (path : depthOutputPath q z) (stage : Fin z)
    (hhalf : (bh12PathParameter q p stage.1
      (bh12PathStage q z path stage)).rate ≤ 1 / 2) :
    bh12PathYieldFactor q p z path stage =
      ((bh12OneLevelProtocolFamily q
        (bh12PathParameter q p stage.1 (bh12PathStage q z path stage)) hhalf).protocol
        (path stage)).run.successProbability := by
  unfold bh12PathYieldFactor
  symm
  exact bh12OneLevelProtocolFamily_successProbability q
    (bh12PathParameter q p stage.1 (bh12PathStage q z path stage)) hhalf
    (path stage)
end QEC.Distillation.Triorthogonal.BH12Concatenation
