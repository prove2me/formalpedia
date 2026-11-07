-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction.coe_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:59:13.979007+00:00
-- url     : https://prove2.me/submissions/15a0bef5-1799-4031-a902-b0cc9d6efa93

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Mathlib.Analysis.Convolution
import Mathlib.LinearAlgebra.Basis.Basic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHeckeAlgebra

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open MeasureTheory Set Function
open scoped LocalTopology MatrixGroups Pointwise Convolution ComplexConjugate
universe u
open QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction
theorem _root_.solution {k : Type u} [Field k] [Finite k] {d : ℕ}
    (f g : HeckeFunction k d) : ⇑(f - g) = ⇑f - ⇑g :=
  rfl
end QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction
