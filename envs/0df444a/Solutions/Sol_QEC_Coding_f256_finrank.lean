-- Prove2me | solution 1 for QEC.Coding.f256_finrank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:36:07.828498+00:00
-- url     : https://prove2.me/submissions/52f22c51-a3a7-4147-af1f-c194c6ff404e

import Mathlib.FieldTheory.Finiteness
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_Field

set_option autoImplicit false
open Polynomial
open QEC QEC.Coding
namespace QEC.Coding
theorem _root_.solution : Module.finrank (ZMod 2) F256 = 8 := by
  simpa [F256, f256Modulus_natDegree] using
    (AdjoinRoot.powerBasis' f256Modulus_monic).finrank
end QEC.Coding
