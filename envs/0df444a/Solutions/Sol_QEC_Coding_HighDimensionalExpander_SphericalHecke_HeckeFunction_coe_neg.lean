-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction.coe_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:59:06.326665+00:00
-- url     : https://prove2.me/submissions/ebc38218-60c0-4583-9b7d-da0e67c4936e

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
    (f : HeckeFunction k d) : ⇑(-f) = -⇑f :=
  rfl
end QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction
