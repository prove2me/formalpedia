-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12Concatenation.bh12OneLevelProtocolFamily_successProbability
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:42:44.067431+00:00
-- url     : https://prove2.me/submissions/5e1b6699-17c3-4f88-96aa-cd78f03f398a

import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_QEC_Distillation_Triorthogonal_Protocol
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_Core_Overhead
import Definitions.Def_QEC_Distillation_Triorthogonal_Concatenation
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12OneLevelProtocolFamily_run

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
    ((bh12OneLevelProtocolFamily q p hhalf).protocol port).run.successProbability =
      rawSuccessMass q p := by
  rw [bh12OneLevelProtocolFamily_run]
  exact bh12ActualRun_successProbability q p
end QEC.Distillation.Triorthogonal.BH12Concatenation
