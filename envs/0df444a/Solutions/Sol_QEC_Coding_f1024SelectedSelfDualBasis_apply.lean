-- Prove2me | solution 1 for QEC.Coding.f1024SelectedSelfDualBasis_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:26:12.267145+00:00
-- url     : https://prove2.me/submissions/41a41cfb-e058-44bb-ba58-8ec0e316ec4e

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
    f1024SelectedSelfDualBasis i =
      (f1024PolynomialBasis ᵥ* f1024SelectedSelfDualP.map (algebraMap (ZMod 2) F1024)) i := by
  rw [f1024SelectedSelfDualBasis, Module.Basis.map_apply, f1024SelectedSelfDualChange]
  change Matrix.toLin f1024PolynomialBasis f1024PolynomialBasis f1024SelectedSelfDualP
      (f1024PolynomialBasis i) = _
  rw [Matrix.toLin_self]
  simp only [Matrix.vecMul, dotProduct, Algebra.smul_def]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm]
  rfl
end QEC.Coding
