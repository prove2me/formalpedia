-- Prove2me | solution 1 for QEC.Coding.f1024SelectedCoordinates_apply_symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:09:08.689444+00:00
-- url     : https://prove2.me/submissions/eb4f4920-4bd1-41ad-8f6e-82471dce5fc0

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
theorem _root_.solution (c : Fin 10 → ZMod 2) :
    f1024SelectedCoordinates (f1024SelectedCoordinates.symm c) = c :=
  f1024SelectedCoordinates.apply_symm_apply c
end QEC.Coding
