-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12Concatenation.depthTwoChildRun_eq_bh12ActualRun
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:41:58.411193+00:00
-- url     : https://prove2.me/submissions/f92afa9a-6a3d-4c79-9db7-b14312d5da2a

import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_QEC_Distillation_Triorthogonal_Protocol
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_Core_Overhead
import Definitions.Def_QEC_Distillation_Triorthogonal_Concatenation
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_depthTwoChildResources_eq_noisyResources

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
    (hsuccess : 0 < rawSuccessMass q p) (port : OddRow q) :
    depthTwoChildRun q p port =
      bh12ActualRun q (bh12DecodedMarginalErrorParameter q p hsuccess port) := by
  unfold depthTwoChildRun bh12ActualRun
  rw [depthTwoChildResources_eq_noisyResources]
end QEC.Distillation.Triorthogonal.BH12Concatenation
