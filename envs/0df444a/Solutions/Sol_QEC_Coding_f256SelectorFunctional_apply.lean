-- Prove2me | solution 1 for QEC.Coding.f256SelectorFunctional_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:24:31.680808+00:00
-- url     : https://prove2.me/submissions/b06f129f-2137-488b-9332-cde603b30970

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_MultiplicationEmbedding
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_ReverseEmbedding
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_Selector

set_option autoImplicit false
open QEC QEC.Coding
namespace QEC.Coding
theorem _root_.solution (v : Fin 512 → ZMod 2) :
    f256SelectorFunctional v = f256RMFEpsi (f256MFEPsi v) := rfl
end QEC.Coding
