-- Prove2me | solution 2 for QEC.Coding.f256TraceAlphaCubed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:50:01.698428+00:00
-- url     : https://prove2.me/submissions/b58a8dd8-4426-49aa-a470-f29258c48ea8

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_SelfDualBasis
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_ReverseEmbedding
import Theorems.Thm_QEC_Coding_f256PolynomialBasis_apply
import Theorems.Thm_QEC_Coding_f256PolynomialTraceMatrix_eq


set_option autoImplicit false
open QEC QEC.Coding
namespace QEC.Coding
theorem _root_.solution :
    Algebra.trace (ZMod 2) F256 (f256Alpha ^ 3) = 1 := by
  have hentry := congr_fun (congr_fun f256PolynomialTraceMatrix_eq 0) 3
  simpa [Algebra.traceMatrix_apply, Algebra.traceForm_apply,
    f256PolynomialBasis_apply, f256PolynomialTraceGram] using hentry
end QEC.Coding
