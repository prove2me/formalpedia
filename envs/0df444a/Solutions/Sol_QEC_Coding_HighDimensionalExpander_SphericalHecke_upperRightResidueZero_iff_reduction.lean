-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.upperRightResidueZero_iff_reduction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:27:20.6799+00:00
-- url     : https://prove2.me/submissions/f1368093-d356-4341-a305-894b91b0cff6

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_FiniteGrassmannian
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_LocalLinkReduction

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped MatrixGroups
open QEC.Coding.HighDimensionalExpander.FiniteGeometry
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
theorem _root_.solution
    (k : Type*) [Field k] (d r : ℕ)
    (g : GL (Fin d) (IntegerRing k)) :
    UpperRightResidueZero k d r g ↔
      ∀ i j : Fin d, i.val < r → r ≤ j.val →
        powerSeriesReductionGL k d g i j = 0 := by
  rfl
end QEC.Coding.HighDimensionalExpander.SphericalHecke
