-- Prove2me | solution 2 for QEC.Coding.f256Alpha_pow_seventeen
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:48:16.382922+00:00
-- url     : https://prove2.me/submissions/83020d0c-55ba-4afa-a738-f5227042c92e

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_Field
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_SelfDualBasis
section
open Polynomial
open scoped Matrix
namespace QEC.Coding
private theorem f256Alpha_pow_eq_mk (k : ℕ) :
    f256Alpha ^ k = AdjoinRoot.mk f256Modulus (X ^ k) := by
  simp [f256Alpha, ← AdjoinRoot.mk_X]
end QEC.Coding
end

set_option autoImplicit false
open Polynomial
open scoped Matrix
open QEC QEC.Coding
namespace QEC.Coding
theorem _root_.solution : f256Alpha ^ 17 = 1 := by
  rw [f256Alpha_pow_eq_mk, ← (AdjoinRoot.mk f256Modulus).map_one,
    AdjoinRoot.mk_eq_mk]
  refine ⟨(X + 1) * (X ^ 8 + X ^ 7 + X ^ 6 + X ^ 4 + X ^ 2 + X + 1), ?_⟩
  simp only [f256Modulus]
  ring_nf
  reduce_mod_char
end QEC.Coding
