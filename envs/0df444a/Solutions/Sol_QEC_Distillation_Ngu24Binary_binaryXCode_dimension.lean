-- Prove2me | solution 1 for QEC.Distillation.Ngu24Binary.binaryXCode_dimension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T12:19:15.809216+00:00
-- url     : https://prove2.me/submissions/9610694c-4a1a-4011-8d2c-7b03012ddc73

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryEncoding
import Definitions.Def_QEC_Coding_Stabilizer_BasisAction
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryCSS
import Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryKernelWordMap_injective

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24Binary
open Coding Semantics Ngu24MultiplicativeCSS
open Coding.AlgebraicGeometry.F256GarciaStichtenoth
open scoped BigOperators
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
namespace QEC.Distillation.Ngu24Binary
theorem _root_.solution (i : Nat) :
    Dimension (binaryXCode i) = Module.finrank (ZMod 2) (f256SourceInput i).H0 :=
  LinearMap.finrank_range_of_inj (binaryKernelWordMap_injective i)
end QEC.Distillation.Ngu24Binary
