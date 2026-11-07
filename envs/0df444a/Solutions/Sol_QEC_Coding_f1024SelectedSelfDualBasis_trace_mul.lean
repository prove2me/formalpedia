-- Prove2me | solution 1 for QEC.Coding.f1024SelectedSelfDualBasis_trace_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:34:38.464354+00:00
-- url     : https://prove2.me/submissions/cc4dfb52-94f7-4542-a5ab-3d1a6971b280

import Definitions.Def_QEC_Coding_QuditQubitConversion_FiniteField
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_QuditQubitConversion_SelfDualBasis
import Theorems.Thm_QEC_Coding_f1024SelectedSelfDualBasis_traceMatrix

set_option autoImplicit false
open Polynomial
open scoped Matrix
open QEC QEC.Coding
namespace QEC.Coding
theorem _root_.solution (i j : Fin 10) :
    Algebra.trace (ZMod 2) F1024 (f1024SelectedSelfDualBasis i * f1024SelectedSelfDualBasis j) =
      if j = i then 1 else 0 := by
  have hentry := congr_fun (congr_fun f1024SelectedSelfDualBasis_traceMatrix i) j
  simpa [Algebra.traceMatrix_apply, Algebra.traceForm_apply, Matrix.one_apply,
    Pi.single_apply, eq_comm] using hentry
end QEC.Coding
