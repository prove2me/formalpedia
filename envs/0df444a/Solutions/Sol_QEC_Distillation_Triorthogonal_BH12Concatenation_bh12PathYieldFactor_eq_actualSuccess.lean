-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12Concatenation.bh12PathYieldFactor_eq_actualSuccess
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T05:35:08.337778+00:00
-- url     : https://prove2.me/submissions/69c7fffe-7129-4c14-b313-c9ae6991d691

import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_QEC_Distillation_Triorthogonal_Protocol
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_Core_Overhead
import Definitions.Def_QEC_Distillation_Triorthogonal_Concatenation
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
theorem _root_.solution (q : Nat) (p : ErrorParameter)
    (z : Nat) (path : depthOutputPath q z) (stage : Fin z) :
    bh12PathYieldFactor q p z path stage =
      (bh12PathRun q p stage.1
        (bh12PathStage q z path stage)).successProbability := by
  change rawSuccessMass q (bh12PathParameter q p stage.1
      (bh12PathStage q z path stage)) =
    (bh12ActualRun q (bh12PathParameter q p stage.1
      (bh12PathStage q z path stage))).successProbability
  exact (bh12ActualRun_successProbability q
    (bh12PathParameter q p stage.1 (bh12PathStage q z path stage))).symm
end QEC.Distillation.Triorthogonal.BH12Concatenation
