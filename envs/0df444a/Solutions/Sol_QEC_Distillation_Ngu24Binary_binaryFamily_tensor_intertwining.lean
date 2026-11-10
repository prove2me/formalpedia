-- Prove2me | solution 1 for QEC.Distillation.Ngu24Binary.binaryFamily_tensor_intertwining
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T12:52:00.670809+00:00
-- url     : https://prove2.me/submissions/9b08461a-8051-4db7-a955-f4f346b13e1a

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryParameters
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinarySelfDual
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryCubicBridge
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryTensorEncoding
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryFamily
import Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryFamily_tagged_intertwining
import Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryTaggedEncodingIsometry_eq_tensorCube


set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24Binary
open Coding Semantics Ngu24MultiplicativeCSS
open Coding.AlgebraicGeometry.F256GarciaStichtenoth
open Filter
namespace QEC.Distillation.Ngu24Binary
theorem _root_.solution (i : Nat)
    (psi : TaggedThreeCopyRegister (ZMod 2) (Fin (f256MultiplicationLogicalCount i))) :
    binaryPhysicalCCZ
        (taggedTensorCube (ZMod 2) (Fin (f256MultiplicationLogicalCount i))
          ((f256SourceInput i).PivotComplement × Fin 512) (binaryEncodingIsometry i).toLinearMap psi) =
      taggedTensorCube (ZMod 2) (Fin (f256MultiplicationLogicalCount i))
        ((f256SourceInput i).PivotComplement × Fin 512) (binaryEncodingIsometry i).toLinearMap
          (binaryLogicalCCZ psi) := by
  rw [← binaryTaggedEncodingIsometry_eq_tensorCube,
    ← binaryTaggedEncodingIsometry_eq_tensorCube]
  exact binaryFamily_tagged_intertwining i psi
end QEC.Distillation.Ngu24Binary
