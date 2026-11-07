-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledCuspParam_mem_source
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:42:00.214959+00:00
-- url     : https://prove2.me/submissions/f3c7e3a4-b5df-4141-9187-fc6c7f3dff18

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactCore
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledCusps

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N]
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)))
    (q : (lpsOriginalFilledCuspPartialEquiv N (lpsOriginalCuspRepresentative N c)).target) :
    lpsOriginalFilledCuspParam N c q∈
      (lpsOriginalFilledCuspPartialEquiv N (lpsOriginalCuspRepresentative N c)).source :=
  (lpsOriginalFilledCuspPartialEquiv N (lpsOriginalCuspRepresentative N c)).mapsTo_symm q.property
end QEC.Coding.TannerLiftedProduct
