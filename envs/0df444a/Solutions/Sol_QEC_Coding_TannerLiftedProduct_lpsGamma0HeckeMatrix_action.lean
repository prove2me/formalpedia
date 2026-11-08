-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsGamma0HeckeMatrix_action
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:30:50.210173+00:00
-- url     : https://prove2.me/submissions/623c58a2-77c8-444f-b8b8-e36d6407191d

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
    (hNp : p.Coprime N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    (lpsGamma0HeckeMatrix N p hNp).mulVec ((lpsGamma0CuspBasis N 2).repr f) =
      (lpsGamma0CuspBasis N 2).repr (lpsCuspHeckeLinearMap N p hNp f) :=
  LinearMap.toMatrix_mulVec_repr _ _ _ _
end QEC.Coding.TannerLiftedProduct
