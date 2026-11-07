-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction.star_fundamentalHeckeFunction_rankThree_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:22:47.115507+00:00
-- url     : https://prove2.me/submissions/90c2f6c5-cc0f-48db-a140-f74b5a0cd97f

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Mathlib.Analysis.Convolution
import Mathlib.LinearAlgebra.Basis.Basic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHeckeAlgebra
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_eq_of_inv
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_fundamentalDoubleCoset_rankThree_two_inv


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
    star (fundamentalHeckeFunction k 3 2) =
      fundamentalHeckeFunction k 3 1 :=
  star_fundamentalHeckeFunction_eq_of_inv k 3 2 1
    (fundamentalDoubleCoset_rankThree_two_inv k)
end QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction
