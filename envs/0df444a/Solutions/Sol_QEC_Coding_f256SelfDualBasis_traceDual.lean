-- Prove2me | solution 1 for QEC.Coding.f256SelfDualBasis_traceDual
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:54:07.972295+00:00
-- url     : https://prove2.me/submissions/eb17b781-dbd1-4725-96d8-a87a7b511c1f

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_Field
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_SelfDualBasis
import Theorems.Thm_QEC_Coding_f256SelfDualBasis_trace_mul

set_option autoImplicit false
open Polynomial
open scoped Matrix
open QEC QEC.Coding
namespace QEC.Coding
theorem _root_.solution :
    f256SelfDualBasis.traceDual = f256SelfDualBasis := by
  have hfun : (f256SelfDualBasis.traceDual : Fin 8 → F256) =
      (f256SelfDualBasis : Fin 8 → F256) := by
    apply Module.Basis.traceDual_eq_iff.mpr
    intro i j
    simpa only [Algebra.traceForm_apply] using f256SelfDualBasis_trace_mul i j
  apply DFunLike.ext _ _
  intro i
  exact congr_fun hfun i
end QEC.Coding
