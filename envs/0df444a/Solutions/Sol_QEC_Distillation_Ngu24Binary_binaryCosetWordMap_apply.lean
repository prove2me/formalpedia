-- Prove2me | solution 1 for QEC.Distillation.Ngu24Binary.binaryCosetWordMap_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T11:48:30.95221+00:00
-- url     : https://prove2.me/submissions/5d974b24-2070-4cda-b313-90bd270542d2

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryEncoding
import Definitions.Def_QEC_Coding_Stabilizer_BasisAction
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryCSS

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24Binary
open Coding Semantics Ngu24MultiplicativeCSS
open Coding.AlgebraicGeometry.F256GarciaStichtenoth
open scoped BigOperators
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
namespace QEC.Distillation.Ngu24Binary
theorem _root_.solution (i : Nat)
    (u : Word (ZMod 2) (Fin (f256MultiplicationLogicalCount i))) (h : (f256SourceInput i).H0) :
    binaryCosetWordMap i (u, h) = physicalWordEmbedding (f256SourceInput i).PivotComplement
      ((f256SourceInput i).shortenedCosetLabel
        (logicalWordEmbedding (Fin (f256MultiplicationLogicalCount i)) u) h) := by
  change physicalWordEmbedding _ ((f256SourceInput i).puncturedLogicalWord
    (logicalWordEmbedding _ u)) + physicalWordEmbedding _ ((f256SourceInput i).puncture h.val.val) = _
  rw [← map_add]
  rfl
end QEC.Distillation.Ngu24Binary
