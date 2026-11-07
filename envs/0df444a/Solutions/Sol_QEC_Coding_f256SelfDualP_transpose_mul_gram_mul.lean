-- Prove2me | solution 1 for QEC.Coding.f256SelfDualP_transpose_mul_gram_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:48:23.1812+00:00
-- url     : https://prove2.me/submissions/2ac1a031-56b1-4eb0-a90f-91a399b0aa3d

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_Field
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_SelfDualBasis

set_option autoImplicit false
open Polynomial
open scoped Matrix
open QEC QEC.Coding
namespace QEC.Coding
theorem _root_.solution :
    f256SelfDualP.transpose * f256PolynomialTraceGram * f256SelfDualP = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide
end QEC.Coding
