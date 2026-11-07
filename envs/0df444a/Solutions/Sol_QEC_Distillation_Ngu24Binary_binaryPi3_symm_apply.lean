-- Prove2me | solution 1 for QEC.Distillation.Ngu24Binary.binaryPi3_symm_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:47:31.408111+00:00
-- url     : https://prove2.me/submissions/1a00991b-6edd-46bd-9c95-823280dd2734

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_Selector
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_Register
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryTriples

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24Binary
open Coding
open scoped BigOperators
universe u
variable (J : Type u)
namespace QEC.Distillation.Ngu24Binary
theorem _root_.solution (j : J) (q : Fin 512) :
    (binaryPi3 J).symm (j, q) = (j, f256MFEpi3 q) := rfl
end QEC.Distillation.Ngu24Binary
