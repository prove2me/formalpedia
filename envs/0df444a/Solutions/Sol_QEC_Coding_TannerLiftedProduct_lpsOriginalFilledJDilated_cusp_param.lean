-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledJDilated_cusp_param
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:10:24.04803+00:00
-- url     : https://prove2.me/submissions/99ad3b0f-c6b7-44ff-a306-4d8f30f36e5d

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJDilationCuspCoefficient_qParam
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCuspParam_nonzero_lift


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N] (hN : 0<N)
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)))
    (q : (lpsOriginalFilledCuspPartialEquiv N (lpsOriginalCuspRepresentative N c)).target)
    (hq0 : q.val≠0) :
    lpsOriginalFilledJDilated N hN (lpsOriginalFilledCuspParam N c q)=
      lpsOriginalJDilationCuspCoefficient N hN (lpsOriginalCuspRepresentative N c) q.val := by
  obtain ⟨τ,hτ,hq⟩ := lpsOriginalFilledCuspParam_nonzero_lift N c q hq0
  rw [hτ]
  change lpsOriginalJDilated N hN
    (Matrix.SpecialLinearGroup.mapGL ℝ (lpsOriginalCuspRepresentative N c) •τ.val)=_
  rw [←lpsOriginalJDilationCuspCoefficient_qParam N hN
    (lpsOriginalCuspRepresentative N c) τ.val,←hq]
end QEC.Coding.TannerLiftedProduct
