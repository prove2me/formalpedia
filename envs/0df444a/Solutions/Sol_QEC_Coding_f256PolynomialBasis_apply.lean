-- Prove2me | solution 1 for QEC.Coding.f256PolynomialBasis_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:10:17.297387+00:00
-- url     : https://prove2.me/submissions/85be7ba8-0165-4f81-82c0-c5b9abee883b

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
theorem _root_.solution (i : Fin 8) :
    f256PolynomialBasis i = f256Alpha ^ (i : ℕ) := by
  rw [f256PolynomialBasis, Module.Basis.reindex_apply,
    (AdjoinRoot.powerBasis' f256Modulus_monic).basis_eq_pow]
  rfl
end QEC.Coding
