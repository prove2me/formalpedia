-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledJReciprocal_cusp_formula
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:13:09.0162+00:00
-- url     : https://prove2.me/submissions/170620f1-81c5-487e-8deb-d0b97f7e61a3

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularEquation
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJNormalization
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledJReciprocal_cusp_nonzero_eq
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledJ_cusp_param


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N] (a : ℂ)
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)))
    (q : (lpsOriginalFilledCuspPartialEquiv N (lpsOriginalCuspRepresentative N c)).target)
    (hq0 : q.val≠0) :
    lpsOriginalFilledJReciprocal N a (lpsOriginalFilledCuspParam N c q)=
      q.val^(lpsOriginalCuspWidthNat N (lpsOriginalCuspRepresentative N c))/
      (lpsOriginalJQCoefficient (q.val^(lpsOriginalCuspWidthNat N
        (lpsOriginalCuspRepresentative N c)))-
        a*q.val^(lpsOriginalCuspWidthNat N (lpsOriginalCuspRepresentative N c))) := by
  let m := lpsOriginalCuspWidthNat N (lpsOriginalCuspRepresentative N c)
  have hqm : q.val^m≠0 := pow_ne_zero m hq0
  have hj := lpsOriginalFilledJ_cusp_param N c q hq0
  have he : lpsOriginalFilledJ N (lpsOriginalFilledCuspParam N c q)=
      lpsOriginalJQCoefficient (q.val^m)/q.val^m :=
    (eq_div_iff hqm).mpr (by rw [mul_comm];exact hj)
  rw [lpsOriginalFilledJReciprocal_cusp_nonzero_eq N a c q hq0,he]
  have hh : lpsOriginalJQCoefficient (q.val^m)/q.val^m-a=
      (lpsOriginalJQCoefficient (q.val^m)-a*q.val^m)/q.val^m := by
    field_simp [hqm]
  rw [hh,inv_div]
end QEC.Coding.TannerLiftedProduct
