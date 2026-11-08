-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsGamma0Cusp_finrank_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:30:48.78469+00:00
-- url     : https://prove2.me/submissions/fc9b90e6-0389-422d-a766-e68242ecd2ce

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCongruenceSturm
import Mathlib.NumberTheory.ModularForms.CuspFormSubmodule
import Mathlib.LinearAlgebra.Matrix.ToLin
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCongruenceFiniteDimension
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsGamma0_finrank_le

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold Pointwise
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N] (k : ℤ) :
    Module.finrank ℂ (CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) ≤
      lpsGamma0CoefficientCount N k := by
  let := lpsGamma0FiniteDimensional N k
  exact (LinearMap.finrank_le_finrank_of_injective CuspForm.toModularFormₗ_injective).trans
    (lpsGamma0_finrank_le N k)
end QEC.Coding.TannerLiftedProduct
