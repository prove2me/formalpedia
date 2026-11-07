-- Prove2me | solution 1 for QEC.Coding.f1024SelectedSelfDualBasis_traceDual
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:35:20.579338+00:00
-- url     : https://prove2.me/submissions/5bc34def-ed86-44f3-bf4c-0faf2aad7423

import Definitions.Def_QEC_Coding_QuditQubitConversion_FiniteField
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_QuditQubitConversion_SelfDualBasis
import Theorems.Thm_QEC_Coding_f1024SelectedSelfDualBasis_trace_mul

set_option autoImplicit false
open Polynomial
open scoped Matrix
open QEC QEC.Coding
namespace QEC.Coding
theorem _root_.solution :
    f1024SelectedSelfDualBasis.traceDual = f1024SelectedSelfDualBasis := by
  have hfun : (f1024SelectedSelfDualBasis.traceDual : Fin 10 → F1024) =
      (f1024SelectedSelfDualBasis : Fin 10 → F1024) := by
    apply Module.Basis.traceDual_eq_iff.mpr
    intro i j
    simpa only [Algebra.traceForm_apply] using f1024SelectedSelfDualBasis_trace_mul i j
  apply DFunLike.ext _ _
  intro i
  exact congr_fun hfun i
end QEC.Coding
