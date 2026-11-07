-- Prove2me | solution 1 for QEC.Distillation.DependentBatch.transposeRouting_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:00:36.060464+00:00
-- url     : https://prove2.me/submissions/a9f84388-5dbb-4a2f-adfb-ae3992d64eb4

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
    transposeRouting n k (parent, port) = (port, parent) :=
  rfl
end QEC.Distillation.DependentBatch
