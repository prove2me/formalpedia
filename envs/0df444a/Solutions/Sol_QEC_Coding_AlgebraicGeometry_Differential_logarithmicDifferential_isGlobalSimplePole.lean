-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.Differential.logarithmicDifferential_isGlobalSimplePole
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:36:23.846838+00:00
-- url     : https://prove2.me/submissions/c2a8cb6e-17d8-4bee-b8c6-9b8a39288c9f

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Global_SimplePoleResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_LogarithmicResidue

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc WithZero
open QEC.Coding.AlgebraicGeometry.Differential
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
namespace QEC.Coding.AlgebraicGeometry.Differential
theorem _root_.solution (f : F) (hf : f ≠ 0) :
    IsGlobalSimplePole (k := k) (F := F)
      (logarithmicDifferential (k := k) (F := F) f) := by
  intro P
  exact (logarithmicDifferentialAtSimplePole
    (k := k) (F := F) P f hf).property
end QEC.Coding.AlgebraicGeometry.Differential
