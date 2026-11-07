-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction.star_fundamentalHeckeFunction_rankFour_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:22:49.125972+00:00
-- url     : https://prove2.me/submissions/97ad477d-23e0-49fa-8381-7bbec0526531

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Mathlib.Analysis.Convolution
import Mathlib.LinearAlgebra.Basis.Basic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHeckeAlgebra
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_eq_of_inv
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_fundamentalDoubleCoset_rankFour_three_inv


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open MeasureTheory Set Function
open scoped LocalTopology MatrixGroups Pointwise Convolution ComplexConjugate
universe u
open QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction
theorem _root_.solution
    (k : Type u) [Field k] [Finite k] :
    star (fundamentalHeckeFunction k 4 3) =
      fundamentalHeckeFunction k 4 1 :=
  star_fundamentalHeckeFunction_eq_of_inv k 4 3 1
    (fundamentalDoubleCoset_rankFour_three_inv k)
end QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction
