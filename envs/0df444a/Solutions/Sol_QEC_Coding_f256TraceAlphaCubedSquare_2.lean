-- Prove2me | solution 2 for QEC.Coding.f256TraceAlphaCubedSquare
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:54:25.163022+00:00
-- url     : https://prove2.me/submissions/607a083b-745c-4388-840c-39ba5ba6c994

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_SelfDualBasis
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_ReverseEmbedding
import Theorems.Thm_QEC_Coding_f256PolynomialBasis_apply
import Theorems.Thm_QEC_Coding_f256PolynomialTraceMatrix_eq


set_option autoImplicit false
open QEC QEC.Coding
namespace QEC.Coding
theorem _root_.solution :
    Algebra.trace (ZMod 2) F256 ((f256Alpha ^ 3) ^ 2) = 1 := by
  have hentry := congr_fun (congr_fun f256PolynomialTraceMatrix_eq 3) 3
  simpa [Algebra.traceMatrix_apply, Algebra.traceForm_apply,
    f256PolynomialBasis_apply, f256PolynomialTraceGram, pow_two] using hentry
end QEC.Coding
