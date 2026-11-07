-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsGamma0HeckePrimePowerMatrix_recover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:51:39.17921+00:00
-- url     : https://prove2.me/submissions/8a2807cd-e229-43f6-b11d-533894b7d285

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCongruenceSturm
import Mathlib.NumberTheory.ModularForms.CuspFormSubmodule
import Mathlib.LinearAlgebra.Matrix.ToLin
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCongruenceFiniteDimension

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold Pointwise
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hNp : p.Coprime N) (r : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    (lpsGamma0CuspBasis N 2).equivFun.symm
      ((lpsGamma0HeckePrimePowerMatrix N p hNp r).mulVec
        ((lpsGamma0CuspBasis N 2).repr f)) = lpsHeckePrimePowerLinearMap N p hNp r f := by
  rw [lpsGamma0HeckePrimePowerMatrix, LinearMap.toMatrix_mulVec_repr]
  exact (lpsGamma0CuspBasis N 2).equivFun.symm_apply_apply _
end QEC.Coding.TannerLiftedProduct
