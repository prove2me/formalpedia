-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.Differential.residueCongruent_symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:45:38.925808+00:00
-- url     : https://prove2.me/submissions/3a76d6aa-1937-4b46-b752-b8be0b293ba8

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_Differential
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RationalPlace
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DifferentialLocal

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped WithZero
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
open QEC.Coding.AlgebraicGeometry.Differential
namespace QEC.Coding.AlgebraicGeometry.Differential
theorem _root_.solution {P : GlobalPlace k F} {omega eta : Differential k F} :
    ResidueCongruent P omega eta -> ResidueCongruent P eta omega := by
  intro h
  rw [ResidueCongruent, OrderAtLeast, smul_sub]
  convert (localDifferentialLattice P).neg_mem (by
    rwa [ResidueCongruent, OrderAtLeast, smul_sub] at h) using 1
  abel_nf
end QEC.Coding.AlgebraicGeometry.Differential
