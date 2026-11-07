-- Prove2me | solution 1 for QEC.Coding.f256SelfDualBasis_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:48:27.526707+00:00
-- url     : https://prove2.me/submissions/25e482a0-cf76-47c7-8592-2c4ebe9cf6db

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
    f256SelfDualBasis i =
      (f256PolynomialBasis ᵥ* f256SelfDualP.map (algebraMap (ZMod 2) F256)) i := by
  rw [f256SelfDualBasis, Module.Basis.map_apply, f256SelfDualChange]
  change Matrix.toLin f256PolynomialBasis f256PolynomialBasis f256SelfDualP
      (f256PolynomialBasis i) = _
  rw [Matrix.toLin_self]
  simp only [Matrix.vecMul, dotProduct, Algebra.smul_def]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm]
  rfl
end QEC.Coding
