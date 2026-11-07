-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledJDilated_cusp_meromorphic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:15:20.492201+00:00
-- url     : https://prove2.me/submissions/e1dae5dc-a585-49b3-b27a-25609702b701

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJDilationCuspCoefficient_meromorphic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledJDilated_cusp_germ

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N] (hN : 0<N)
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :
    MeromorphicAt (fun q : ℂ => lpsOriginalFilledJDilated N hN
      ((lpsOriginalFilledCuspPartialEquiv N (lpsOriginalCuspRepresentative N c)).symm q)) 0 := by
  exact (lpsOriginalJDilationCuspCoefficient_meromorphic N hN
    (lpsOriginalCuspRepresentative N c)).congr (lpsOriginalFilledJDilated_cusp_germ N hN c).symm
end QEC.Coding.TannerLiftedProduct
