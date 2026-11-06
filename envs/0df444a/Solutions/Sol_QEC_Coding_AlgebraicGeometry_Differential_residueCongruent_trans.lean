-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.Differential.residueCongruent_trans
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:15:13.643824+00:00
-- url     : https://prove2.me/submissions/db012ab8-c5ac-4453-86c4-259ca550d4c3

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_Differential
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RationalPlace
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DifferentialLocal
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_residueCongruent_refl
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_residueCongruent_symm
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply


attribute [local refl] QEC.Coding.AlgebraicGeometry.Differential.residueCongruent_refl
attribute [local symm] QEC.Coding.AlgebraicGeometry.Differential.residueCongruent_symm

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped WithZero
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
open QEC.Coding.AlgebraicGeometry.Differential
namespace QEC.Coding.AlgebraicGeometry.Differential
theorem _root_.solution {P : GlobalPlace k F}
    {omega eta theta : Differential k F} :
    ResidueCongruent P omega eta -> ResidueCongruent P eta theta ->
      ResidueCongruent P omega theta := by
  intro homegaeta hetatheta
  have hsum := (localDifferentialLattice P).add_mem homegaeta hetatheta
  simpa only [ResidueCongruent, OrderAtLeast, smul_sub, sub_add_sub_cancel] using hsum
end QEC.Coding.AlgebraicGeometry.Differential
