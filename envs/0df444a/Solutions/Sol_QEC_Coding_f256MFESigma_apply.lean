-- Prove2me | solution 1 for QEC.Coding.f256MFESigma_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:09:31.059206+00:00
-- url     : https://prove2.me/submissions/63afd4ad-16ca-4f63-954c-1d69fe26b345

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_SelfDualBasis
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_MultiplicationEmbedding

set_option autoImplicit false
open QEC QEC.Coding
namespace QEC.Coding
theorem _root_.solution (x : F256) (i j k : Fin 8) :
    f256MFESigma x (f256MFEIndex i j k) = f256PolynomialBasis.equivFun x i := by
  simp [f256MFESigma, f256MFEIndex]
end QEC.Coding
