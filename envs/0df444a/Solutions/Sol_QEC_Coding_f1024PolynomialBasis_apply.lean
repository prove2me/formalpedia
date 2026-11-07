-- Prove2me | solution 1 for QEC.Coding.f1024PolynomialBasis_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:25:57.852194+00:00
-- url     : https://prove2.me/submissions/7a0bb34a-e207-4acc-9651-becf96420260

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
theorem _root_.solution (i : Fin 10) :
    f1024PolynomialBasis i = f1024Alpha ^ (i : ℕ) := by
  rw [f1024PolynomialBasis, Module.Basis.reindex_apply,
    (AdjoinRoot.powerBasis' f1024Modulus_monic).basis_eq_pow]
  rfl
end QEC.Coding
