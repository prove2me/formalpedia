-- Prove2me | solution 1 for QEC.Coding.f256SelfDualBasis_traceMatrix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:50:00.652106+00:00
-- url     : https://prove2.me/submissions/b0767ef2-1d73-4f34-a988-4a4e14f3bf0c

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_Field
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_SelfDualBasis
import Theorems.Thm_QEC_Coding_f256PolynomialTraceMatrix_eq
import Theorems.Thm_QEC_Coding_f256SelfDualP_transpose_mul_gram_mul
import Theorems.Thm_QEC_Coding_f256SelfDualBasis_apply

set_option autoImplicit false
open Polynomial
open scoped Matrix
open QEC QEC.Coding
namespace QEC.Coding
theorem _root_.solution :
    Algebra.traceMatrix (ZMod 2) f256SelfDualBasis = 1 := by
  have hbasis : (f256SelfDualBasis : Fin 8 → F256) =
      f256PolynomialBasis ᵥ* f256SelfDualP.map (algebraMap (ZMod 2) F256) := by
    funext i
    exact f256SelfDualBasis_apply i
  calc
    Algebra.traceMatrix (ZMod 2) f256SelfDualBasis =
        Algebra.traceMatrix (ZMod 2)
          (f256PolynomialBasis ᵥ* f256SelfDualP.map (algebraMap (ZMod 2) F256)) := by
            rw [hbasis]
    _ = f256SelfDualP.transpose * Algebra.traceMatrix (ZMod 2) f256PolynomialBasis *
        f256SelfDualP :=
          Algebra.traceMatrix_of_matrix_vecMul f256PolynomialBasis f256SelfDualP
    _ = f256SelfDualP.transpose * f256PolynomialTraceGram * f256SelfDualP := by
          rw [f256PolynomialTraceMatrix_eq]
    _ = 1 := f256SelfDualP_transpose_mul_gram_mul
end QEC.Coding
