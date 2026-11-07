-- Prove2me | solution 1 for QEC.Coding.f1024SelectedSelfDualBasis_traceMatrix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:33:59.311011+00:00
-- url     : https://prove2.me/submissions/1a120574-37c9-4bfc-adce-fc65d2b011b3

import Definitions.Def_QEC_Coding_QuditQubitConversion_FiniteField
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_QuditQubitConversion_SelfDualBasis
import Theorems.Thm_QEC_Coding_f1024PolynomialTraceMatrix_eq
import Theorems.Thm_QEC_Coding_f1024SelectedSelfDualP_transpose_mul_gram_mul
import Theorems.Thm_QEC_Coding_f1024SelectedSelfDualBasis_apply

set_option autoImplicit false
open Polynomial
open scoped Matrix
open QEC QEC.Coding
namespace QEC.Coding
theorem _root_.solution :
    Algebra.traceMatrix (ZMod 2) f1024SelectedSelfDualBasis = 1 := by
  have hbasis : (f1024SelectedSelfDualBasis : Fin 10 → F1024) =
      f1024PolynomialBasis ᵥ* f1024SelectedSelfDualP.map (algebraMap (ZMod 2) F1024) := by
    funext i
    exact f1024SelectedSelfDualBasis_apply i
  calc
    Algebra.traceMatrix (ZMod 2) f1024SelectedSelfDualBasis =
        Algebra.traceMatrix (ZMod 2)
          (f1024PolynomialBasis ᵥ* f1024SelectedSelfDualP.map (algebraMap (ZMod 2) F1024)) := by
            rw [hbasis]
    _ = f1024SelectedSelfDualP.transpose * Algebra.traceMatrix (ZMod 2) f1024PolynomialBasis *
        f1024SelectedSelfDualP :=
          Algebra.traceMatrix_of_matrix_vecMul f1024PolynomialBasis f1024SelectedSelfDualP
    _ = f1024SelectedSelfDualP.transpose * f1024PolynomialTraceGram * f1024SelectedSelfDualP := by
          rw [f1024PolynomialTraceMatrix_eq]
    _ = 1 := f1024SelectedSelfDualP_transpose_mul_gram_mul
end QEC.Coding
