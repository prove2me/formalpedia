-- Prove2me | solution 1 for QEC.Coding.f1024SelectedSelfDualPInv_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:09:06.13085+00:00
-- url     : https://prove2.me/submissions/3b981ba5-16f8-4c47-a36c-5f2ce8f3b73e

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
    f1024SelectedSelfDualPInv * f1024SelectedSelfDualP = 1 := by decide
end QEC.Coding
