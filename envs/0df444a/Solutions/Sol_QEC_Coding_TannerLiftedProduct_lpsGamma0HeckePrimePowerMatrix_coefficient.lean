-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsGamma0HeckePrimePowerMatrix_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:31:08.886203+00:00
-- url     : https://prove2.me/submissions/67f0981a-0b0c-4ac6-8e32-e89d78008fdd

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCongruenceSturm
import Mathlib.NumberTheory.ModularForms.CuspFormSubmodule
import Mathlib.LinearAlgebra.Matrix.ToLin
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCongruenceFiniteDimension
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsGamma0HeckePrimePowerMatrix_recover
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_one_lpsHeckePrimePowerLinearMap


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold Pointwise
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hNp : p.Coprime N) (r : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    PowerSeries.coeff 1 (UpperHalfPlane.qExpansion 1
      ((lpsGamma0CuspBasis N 2).equivFun.symm
        ((lpsGamma0HeckePrimePowerMatrix N p hNp r).mulVec
          ((lpsGamma0CuspBasis N 2).repr f)))) =
      PowerSeries.coeff (p^r) (UpperHalfPlane.qExpansion 1 f) := by
  rw [lpsGamma0HeckePrimePowerMatrix_recover]
  exact coeff_one_lpsHeckePrimePowerLinearMap N p hNp r f
end QEC.Coding.TannerLiftedProduct
