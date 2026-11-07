-- Prove2me | solution 2 for QEC.Coding.f256Alpha_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:54:04.34794+00:00
-- url     : https://prove2.me/submissions/a7803913-e6d7-4951-a371-41a38636c438

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
theorem _root_.solution : f256Alpha ≠ 1 := by
  intro h
  have hroot := AdjoinRoot.eval₂_root f256Modulus
  have h' : AdjoinRoot.root f256Modulus = 1 := by simpa [f256Alpha] using h
  rw [h'] at hroot
  norm_num [f256Modulus, eval₂_add, eval₂_pow, eval₂_X, eval₂_one, eval₂_C] at hroot
  exact (by norm_num : ¬ 2 ∣ 5) ((CharP.cast_eq_zero_iff F256 2 5).mp hroot)
end QEC.Coding
