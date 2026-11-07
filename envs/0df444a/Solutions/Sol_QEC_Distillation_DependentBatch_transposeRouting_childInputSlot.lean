-- Prove2me | solution 1 for QEC.Distillation.DependentBatch.transposeRouting_childInputSlot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:19:06.27458+00:00
-- url     : https://prove2.me/submissions/300224b9-de93-4ef9-a458-c76fd45277a7

import Definitions.Def_QEC_Distillation_Core_Overhead
import Definitions.Def_QEC_Distillation_Core_DependentBatch

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.DependentBatch
open Semantics
open scoped BigOperators
universe u v
namespace QEC.Distillation.DependentBatch
theorem _root_.solution {n k : Nat}
    (parent : Fin n) (port : Fin k) :
    transposeRouting n k (childInputSlot port parent) = (port, parent) :=
  rfl
end QEC.Distillation.DependentBatch
