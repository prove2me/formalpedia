-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.QuaternionGenerators.coefficientEmbedding_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:48:49.499192+00:00
-- url     : https://prove2.me/submissions/61da63c8-e5ae-4ecb-a3db-a53945b3fe60

import Definitions.Def_QEC_Coding_ExpanderCodes_QuaternionCayleySets
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.GroupTheory.Coset.Card
import Lean.Elab.Tactic.Omega
import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticTorus

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.QuaternionGenerators
open scoped QuadraticAlgebra
universe u v
variable {F : Type u} {K : Type v} [Field F] [Field K]
namespace QEC.Coding.ExpanderCodes.QuaternionGenerators
theorem _root_.solution (f : F →+* K) (epsilon : F) (y : K) :
    Function.Injective (coefficientEmbedding f epsilon y) := by
  intro a b h
  ext
  · exact f.injective (congrArg QuaternionAlgebra.re h)
  · exact f.injective (congrArg QuaternionAlgebra.imI h)
end QEC.Coding.ExpanderCodes.QuaternionGenerators
