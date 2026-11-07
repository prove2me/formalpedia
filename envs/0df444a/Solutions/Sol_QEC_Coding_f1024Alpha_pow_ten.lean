-- Prove2me | solution 1 for QEC.Coding.f1024Alpha_pow_ten
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:25:48.231696+00:00
-- url     : https://prove2.me/submissions/7d5370bc-25ae-49c3-9469-ae43a757e52d

import Mathlib.FieldTheory.Finiteness
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_QuditQubitConversion_FiniteField
section
open Polynomial
namespace QEC.Coding
private theorem f1024Alpha_pow_eq_mk (k : ℕ) :
    f1024Alpha ^ k = AdjoinRoot.mk f1024Modulus (X ^ k) := by
  simp [f1024Alpha, ← AdjoinRoot.mk_X]
end QEC.Coding
end

set_option autoImplicit false
open Polynomial
open QEC QEC.Coding
namespace QEC.Coding
theorem _root_.solution : f1024Alpha ^ 10 = 1 + f1024Alpha ^ 3 := by
  rw [f1024Alpha_pow_eq_mk]
  conv_rhs =>
    rw [← (AdjoinRoot.mk f1024Modulus).map_one, f1024Alpha_pow_eq_mk,
      ← (AdjoinRoot.mk f1024Modulus).map_add]
  rw [AdjoinRoot.mk_eq_mk]
  refine ⟨1, ?_⟩
  simp only [f1024Modulus]
  ring_nf
  reduce_mod_char
end QEC.Coding
