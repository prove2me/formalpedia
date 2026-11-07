-- Prove2me | solution 1 for QEC.Coding.f256MFEPsi_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:24:04.854201+00:00
-- url     : https://prove2.me/submissions/8356d0ab-56d7-41a3-b5f8-093cb377c65c

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_SelfDualBasis
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_MultiplicationEmbedding

set_option autoImplicit false
open QEC QEC.Coding
namespace QEC.Coding
theorem _root_.solution (v : Fin 512 → ZMod 2) :
    f256MFEPsi v =
      ∑ i : Fin 8, ∑ j : Fin 8, ∑ k : Fin 8,
        v (f256MFEIndex i j k) •
          (f256PolynomialBasis i * f256PolynomialBasis j * f256PolynomialBasis k) := rfl
end QEC.Coding
