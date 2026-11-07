-- Prove2me | solution 1 for QEC.Distillation.Ngu24Binary.binaryPi2_symm_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:47:24.362668+00:00
-- url     : https://prove2.me/submissions/b97dc701-3566-4cf4-afbf-2df84e85a26d

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
    (binaryPi2 J).symm (j, q) = (j, f256MFEpi2 q) := rfl
end QEC.Distillation.Ngu24Binary
