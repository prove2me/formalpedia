-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledCuspParam_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:41:58.95062+00:00
-- url     : https://prove2.me/submissions/59d13b00-4e73-48ab-9e41-96c2772e605a

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
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :
    Function.Injective (lpsOriginalFilledCuspParam N c) := by
  intro q q' he
  apply Subtype.ext
  exact (lpsOriginalFilledCuspPartialEquiv N
    (lpsOriginalCuspRepresentative N c)).symm.injOn q.property q'.property he
end QEC.Coding.TannerLiftedProduct
