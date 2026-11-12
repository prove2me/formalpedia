-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12Concatenation.bh12OneLevelProtocolFamily_inputResourceCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:31:36.327426+00:00
-- url     : https://prove2.me/submissions/b4fd2fbb-bea8-4e76-b43d-7e3a2a00e3e4

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
theorem _root_.solution (q : Nat)
    (p : ErrorParameter) (hhalf : p.rate ≤ 1 / 2) (port : OddRow q) :
    (bh12OneLevelProtocolFamily q p hhalf).inputResourceCount port =
      bh12InputCount q :=
  rfl
end QEC.Distillation.Triorthogonal.BH12Concatenation
