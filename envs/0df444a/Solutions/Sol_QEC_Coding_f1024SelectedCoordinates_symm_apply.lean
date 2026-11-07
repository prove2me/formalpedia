-- Prove2me | solution 1 for QEC.Coding.f1024SelectedCoordinates_symm_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:09:07.429207+00:00
-- url     : https://prove2.me/submissions/ecffd35e-f238-4102-936f-0685f042925d

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
theorem _root_.solution (x : F1024) :
    f1024SelectedCoordinates.symm (f1024SelectedCoordinates x) = x :=
  f1024SelectedCoordinates.symm_apply_apply x
end QEC.Coding
