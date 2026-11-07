-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledJ_cusp_param
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:19:00.692706+00:00
-- url     : https://prove2.me/submissions/ad2a574c-76ea-4375-8baa-b0bd768382fa

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledConnected
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import Mathlib.Analysis.Meromorphic.Order
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularFunction
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJInvariant_qParam_pullback
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalQParam_width_pow
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspWidthNat_positive
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspWidthNat_cast
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCuspParam_nonzero_lift


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N]
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)))
    (q : (lpsOriginalFilledCuspPartialEquiv N (lpsOriginalCuspRepresentative N c)).target)
    (hq0 : q.val≠0) :
    q.val^(lpsOriginalCuspWidthNat N (lpsOriginalCuspRepresentative N c)) *
      lpsOriginalFilledJ N (lpsOriginalFilledCuspParam N c q)=
      lpsOriginalJQCoefficient
        (q.val^(lpsOriginalCuspWidthNat N (lpsOriginalCuspRepresentative N c))) := by
  let r := lpsOriginalCuspRepresentative N c
  let m := lpsOriginalCuspWidthNat N r
  obtain ⟨τ,hτ,hq⟩ := lpsOriginalFilledCuspParam_nonzero_lift N c q hq0
  have hpow : q.val^m=Function.Periodic.qParam 1 (τ.val:ℂ) := by
    rw [hq,lpsOriginalCuspWidthNat_cast]
    exact lpsOriginalQParam_width_pow m (lpsOriginalCuspWidthNat_positive N r) τ.val
  have hJ : lpsOriginalFilledJ N (lpsOriginalFilledCuspParam N c q)=
      lpsOriginalJInvariant τ.val := by
    rw [hτ]
    change lpsOriginalJInvariant (Matrix.SpecialLinearGroup.mapGL ℝ r • τ.val)=_
    exact lpsOriginalJInvariant_SL_invariant _ ⟨r,rfl⟩ τ.val
  change q.val^m*lpsOriginalFilledJ N (lpsOriginalFilledCuspParam N c q)=
    lpsOriginalJQCoefficient (q.val^m)
  rw [hJ,hpow]
  exact lpsOriginalJInvariant_qParam_pullback τ.val
end QEC.Coding.TannerLiftedProduct
