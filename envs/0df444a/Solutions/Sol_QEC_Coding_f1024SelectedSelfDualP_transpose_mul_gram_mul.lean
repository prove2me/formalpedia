-- Prove2me | solution 1 for QEC.Coding.f1024SelectedSelfDualP_transpose_mul_gram_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:26:06.544919+00:00
-- url     : https://prove2.me/submissions/cc2c49bc-d573-4675-b5cd-be136dd3a578

import Definitions.Def_QEC_Coding_QuditQubitConversion_FiniteField
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_QuditQubitConversion_SelfDualBasis

set_option autoImplicit false
open Polynomial
open scoped Matrix
open QEC QEC.Coding
namespace QEC.Coding
theorem _root_.solution :
    f1024SelectedSelfDualP.transpose * f1024PolynomialTraceGram * f1024SelectedSelfDualP = 1 := by decide
end QEC.Coding
