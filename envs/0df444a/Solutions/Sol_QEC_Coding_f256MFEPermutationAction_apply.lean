-- Prove2me | solution 1 for QEC.Coding.f256MFEPermutationAction_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:24:08.562003+00:00
-- url     : https://prove2.me/submissions/28da868b-d634-4ba3-abd8-cf5e66868cf7

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_SelfDualBasis
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_MultiplicationEmbedding

set_option autoImplicit false
open QEC QEC.Coding
namespace QEC.Coding
theorem _root_.solution (pi : Equiv.Perm (Fin 512))
    (v : Fin 512 → ZMod 2) (q : Fin 512) :
    f256MFEPermutationAction pi v q = v (pi q) := rfl
end QEC.Coding
