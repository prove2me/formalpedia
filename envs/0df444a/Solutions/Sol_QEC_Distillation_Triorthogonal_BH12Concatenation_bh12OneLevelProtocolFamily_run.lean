-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12Concatenation.bh12OneLevelProtocolFamily_run
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:39:56.170335+00:00
-- url     : https://prove2.me/submissions/5f009ddc-4c59-478c-bd0f-c6ca363aab67

import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_QEC_Distillation_Triorthogonal_Protocol
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_Core_Overhead
import Definitions.Def_QEC_Distillation_Triorthogonal_Concatenation

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
    (hhalf : p.rate ≤ 1 / 2) (port : OddRow q) :
    ((bh12OneLevelProtocolFamily q p hhalf).protocol port).run =
      bh12ActualRun q p :=
  rfl
end QEC.Distillation.Triorthogonal.BH12Concatenation
