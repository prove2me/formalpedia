-- Prove2me | solution 1 for QEC.Coding.f1024_finrank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:11:10.965189+00:00
-- url     : https://prove2.me/submissions/b0cf0df8-c489-4a93-adbf-3d4e196916d4

import Mathlib.FieldTheory.Finiteness
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_QuditQubitConversion_FiniteField

set_option autoImplicit false
open Polynomial
open QEC QEC.Coding
namespace QEC.Coding
theorem _root_.solution : Module.finrank (ZMod 2) F1024 = 10 := by
  simpa [F1024, f1024Modulus_natDegree] using
    (AdjoinRoot.powerBasis' f1024Modulus_monic).finrank
end QEC.Coding
